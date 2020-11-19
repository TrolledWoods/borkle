pub mod ast;
mod context;
mod lexer;
mod token_stream;

use crate::dependencies::DependencyKind;
use crate::errors::ErrorCtx;
use crate::locals::Local;
use crate::operators::{AccessOp, BinaryOp};
pub use ast::{Node, NodeKind};
use bump_tree::Tree;
use context::{DataContext, ImperativeContext};
use lexer::{Bracket, Keyword, TokenKind};
use ustr::Ustr;

pub type Ast = Tree<Node>;
type NodeBuilder<'a> = bump_tree::NodeBuilder<'a, Node>;

pub fn process_string(errors: &mut ErrorCtx, file: Ustr, string: &str) -> Result<(), ()> {
    let mut tokens = lexer::process_string(errors, file, string)?;

    let mut context = DataContext::new(errors, &mut tokens);

    while context
        .tokens
        .try_consume(&TokenKind::Keyword(Keyword::Const))
    {
        constant(&mut context)?;
    }

    Ok(())
}

fn constant(global: &mut DataContext<'_>) -> Result<(), ()> {
    let token = global.tokens.expect_next(global.errors)?;
    if let TokenKind::Identifier(name) = token.kind {
        if global.tokens.try_consume_operator_string("=").is_none() {
            global.error(token.loc, "Expected '=' after const".to_string());
            return Err(());
        }

        let mut ast = Ast::new();

        let mut imperative = ImperativeContext::new();
        expression(global, &mut imperative, ast.builder())?;
        let dependencies = imperative.dependencies;
        ast.set_root();

        println!();
        println!("--- {}", name);
        println!("{:?}", dependencies);
        println!("{:#?}", ast);

        global
            .tokens
            .expect_next_is(global.errors, &TokenKind::SemiColon)?;

        Ok(())
    } else {
        global.error(token.loc, "Expected identifier".to_string());
        Err(())
    }
}

fn expression(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext,
    mut node: NodeBuilder<'_>,
) -> Result<(), ()> {
    value(global, imperative, node.arg())?;

    let mut old_op: Option<BinaryOp> = None;
    while let Some((loc, op, meta_data)) = global.tokens.try_consume_operator_with_metadata() {
        if !meta_data.cleared_operator_string {
            global.errors.warning(
                loc,
                "Ambiguous operator separation, please insert a space to clearly indicate \
                where the binary operator ends and the unary operators begin"
                    .to_string(),
            );
        }

        if old_op.unwrap_or(op).precedence() != op.precedence() {
            global.error(
                loc,
                "Only operators with the same precedence can be used after one another".to_string(),
            );
            return Err(());
        }

        value(global, imperative, node.arg())?;
        node.collapse(Node::new(loc, NodeKind::Binary(op)), 2);
        old_op = Some(op);
    }

    node.into_arg();
    Ok(())
}

/// A value allows for unary operators and member accesses or function insertions.
/// However, unary operators are only allowed before the accesses.
fn value(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext,
    mut node: NodeBuilder<'_>,
) -> Result<(), ()> {
    if let Some((loc, op)) = global.tokens.try_consume_operator() {
        value(global, imperative, node.arg())?;
        node.set(Node::new(loc, NodeKind::Unary(op)));
        node.validate();
    } else {
        member_value(global, imperative, node)?;
    }

    Ok(())
}

/// A member value only allows for member accesses or function insertions. It does not
/// allow for unary operators.
fn member_value(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext,
    mut node: NodeBuilder<'_>,
) -> Result<(), ()> {
    atom_value(global, imperative, node.arg())?;

    while let Some((loc, op)) = global.tokens.try_consume_operator() {
        match op {
            AccessOp::Member => {
                let token = global.tokens.expect_next(global.errors)?;
                if let TokenKind::Identifier(name) = token.kind {
                    node.collapse(Node::new(token.loc, NodeKind::Member(name)), 1);
                } else {
                    global.error(token.loc, "Expected identifier".to_string());
                }
            }
            AccessOp::FunctionInsert => {
                member_value(global, imperative, node.arg())?;
                node.collapse(Node::new(loc, NodeKind::FunctionInsert), 2);
            }
        }
    }

    node.into_arg();
    Ok(())
}

/// A value without unary operators, member accesses, or anything like that.
fn atom_value(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext,
    mut node: NodeBuilder<'_>,
) -> Result<(), ()> {
    let token = global.tokens.expect_next(global.errors)?;
    match token.kind {
        TokenKind::Identifier(name) => {
            if let Some(local_id) = imperative.get_local(name) {
                node.set(Node::new(token.loc, NodeKind::Local(local_id)));
                node.validate();
            } else {
                imperative.dependencies.add(name, DependencyKind::Type);
                node.set(Node::new(token.loc, NodeKind::Global(name)));
                node.validate();
            }
        }

        TokenKind::Literal(literal) => node.set(Node::new(token.loc, NodeKind::Literal(literal))),

        TokenKind::Keyword(Keyword::Let) => {
            let token = global.tokens.expect_next(global.errors)?;
            if let TokenKind::Identifier(name) = token.kind {
                let id = imperative.insert_local(Local {
                    loc: token.loc,
                    name,
                });

                global
                    .tokens
                    .try_consume_operator_string("=")
                    .ok_or_else(|| {
                        global.error(token.loc, "Expected '=' after identifier".into());
                    })?;

                expression(global, imperative, node.arg())?;

                node.set(Node::new(token.loc, NodeKind::Declare(id)));
                node.validate();
            } else {
                global.error(token.loc, "Expected identifier".to_string());
                return Err(());
            }
        }

        TokenKind::Keyword(Keyword::Defer) => {
            let mut ast = Ast::new();
            expression(global, imperative, ast.builder())?;
            ast.set_root();
            imperative.push_defer(ast);

            node.set(Node::new(token.loc, NodeKind::Empty));
            node.validate();
        }

        TokenKind::Open(Bracket::Round) => {
            let mut has_comma = false;
            loop {
                if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
                    break;
                }

                expression(global, imperative, node.arg())?;

                let token = global.tokens.expect_next(global.errors)?;
                match token.kind {
                    TokenKind::Close(Bracket::Round) => break,
                    TokenKind::Comma => has_comma = true,
                    _ => {
                        global.error(token.loc, "Expected either ',' or ')'".to_string());
                        return Err(());
                    }
                }
            }

            if has_comma {
                // A tuple
                node.set(Node::new(token.loc, NodeKind::Tuple));
                node.validate();
            } else {
                // Just a parenthesis
                node.into_arg();
            }
        }

        TokenKind::Open(Bracket::Curly) => {
            node.set(Node::new(token.loc, NodeKind::Block));
            let scope_boundary = imperative.push_scope_boundary();

            while !global.tokens.try_consume(&TokenKind::Close(Bracket::Curly)) {
                if global
                    .tokens
                    .try_consume(&TokenKind::Keyword(Keyword::Const))
                {
                    constant(global)?;
                } else {
                    expression(global, imperative, node.arg())?;
                    global
                        .tokens
                        .expect_next_is(global.errors, &TokenKind::SemiColon)?;
                }
            }

            // Insert deferred definitions.
            for deferred in imperative.defers_to(scope_boundary) {
                node.arg().set_cloned(&deferred.root().unwrap());
            }

            imperative.pop_scope_boundary();
            node.validate();
        }

        _ => {
            global.error(
                token.loc,
                format!("Unexpected token '{:?}', expected value", token.kind),
            );
            return Err(());
        }
    }
    Ok(())
}
