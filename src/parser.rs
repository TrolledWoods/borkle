pub mod ast;
mod context;
mod lexer;
mod token_stream;

use crate::dependencies::{DependencyKind, DependencyList};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::locals::Local;
use crate::operators::{AccessOp, BinaryOp};
use crate::program::{Program, Task};
use crate::types::TypeKind;
pub use ast::{Node, NodeKind};
use bump_tree::Tree;
use context::{DataContext, ImperativeContext};
use lexer::{Bracket, Keyword, TokenKind};
use ustr::Ustr;

pub type Ast = Tree<Node>;
type NodeBuilder<'a> = bump_tree::NodeBuilder<'a, Node>;

pub fn process_string(
    errors: &mut ErrorCtx,
    program: &Program,
    file: Ustr,
    string: &str,
) -> Result<(), ()> {
    let mut tokens = lexer::process_string(errors, file, string)?;

    let mut context = DataContext::new(errors, program, &mut tokens);

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
        let locals = imperative.locals;
        ast.set_root();

        global
            .program
            .insert(name, dependencies, |id| Task::Type(id, locals, ast));

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

    if let Some(loc) = global.tokens.try_consume_operator_string(":") {
        type_(global, &mut imperative.dependencies, node.arg())?;
        node.set(Node::new(loc, NodeKind::TypeBound));
        node.validate();
    } else {
        node.into_arg();
    }
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

    while let Some((_, op)) = global.tokens.try_consume_operator() {
        match op {
            AccessOp::Member => {
                let token = global.tokens.expect_next(global.errors)?;
                if let TokenKind::Identifier(name) = token.kind {
                    node.collapse(Node::new(token.loc, NodeKind::Member(name)), 1);
                } else {
                    global.error(token.loc, "Expected identifier".to_string());
                }
            }
        }
    }

    node.into_arg();
    Ok(())
}

fn type_(
    global: &mut DataContext<'_>,
    dependencies: &mut DependencyList,
    mut node: NodeBuilder<'_>,
) -> Result<(), ()> {
    let token = global.tokens.expect_next(global.errors)?;
    match token.kind {
        TokenKind::Identifier(name) => {
            dependencies.add(name, DependencyKind::Value);
            node.set(Node::new(token.loc, NodeKind::Global(name)));
            node.validate();
        }
        TokenKind::Keyword(Keyword::I64) => {
            node.set(Node::new(
                token.loc,
                NodeKind::LiteralType(TypeKind::I64.into()),
            ));
            node.validate();
        }
        TokenKind::Keyword(Keyword::U8) => {
            node.set(Node::new(
                token.loc,
                NodeKind::LiteralType(TypeKind::U8.into()),
            ));
            node.validate();
        }
        _ => {
            global.error(
                token.loc,
                "Unexpected token, expected type expression".to_string(),
            );
            return Err(());
        }
    }

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
                    type_: None,
                    value: None,
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
            {
                let mut builder = ast.builder();
                builder.set(Node::new(token.loc, NodeKind::Block));

                imperative.push_scope_boundary();
                expression(global, imperative, builder.arg())?;
                imperative.pop_scope_boundary(&mut builder);
            }
            ast.set_root();
            imperative.push_defer(ast);

            node.set(Node::new(token.loc, NodeKind::Empty));
            node.validate();
        }
        TokenKind::Keyword(Keyword::Extern) => {
            let loc = token.loc;
            let token = global.tokens.expect_next(global.errors)?;
            if let TokenKind::Literal(Literal::String(library_name)) = token.kind {
                let token = global.tokens.expect_next(global.errors)?;
                if let TokenKind::Literal(Literal::String(symbol_name)) = token.kind {
                    node.set(Node::new(
                        loc,
                        NodeKind::Extern {
                            library_name,
                            symbol_name,
                        },
                    ));
                    node.validate();
                } else {
                    global.error(
                        token.loc,
                        "Expected string literal containing the library name".to_string(),
                    );
                    return Err(());
                }
            } else {
                global.error(
                    token.loc,
                    "Expected string literal containing the library name".to_string(),
                );
                return Err(());
            }
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
                // node.set(Node::new(token.loc, NodeKind::Tuple));
                // node.validate();
                todo!("Tuples");
            } else {
                // Just a parenthesis
                node.into_arg();
            }
        }

        TokenKind::Open(Bracket::Curly) => {
            imperative.push_scope_boundary();

            loop {
                if let Some(loc) = global
                    .tokens
                    .try_consume_with_data(&TokenKind::Close(Bracket::Curly))
                {
                    node.arg().set(Node::new(loc, NodeKind::Empty));
                    break;
                }

                if global
                    .tokens
                    .try_consume(&TokenKind::Keyword(Keyword::Const))
                {
                    constant(global)?;
                } else {
                    expression(global, imperative, node.arg())?;

                    let token = global.tokens.expect_next(global.errors)?;
                    match token.kind {
                        TokenKind::SemiColon => {}
                        TokenKind::Close(Bracket::Curly) => break,
                        _ => {
                            global.error(token.loc, "Expected ';' or '}'".to_string());
                            return Err(());
                        }
                    }
                }
            }

            imperative.pop_scope_boundary(&mut node);
            node.set(Node::new(token.loc, NodeKind::Block));
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

/// Tries to parse a type marker. It first checks if there is a ':',
/// and only tries to parse a type if there is one. If there was a type
/// marker here, it returns Ok(true), if not it returns Ok(false)
fn maybe_type_marker(
    global: &mut DataContext<'_>,
    dependencies: &mut DependencyList,
    mut node: NodeBuilder<'_>,
) -> Result<bool, ()> {
    if global.tokens.try_consume_operator_string(":").is_none() {
        return Ok(false);
    }

    let token = global.tokens.expect_next(global.errors)?;
    match token.kind {
        TokenKind::Identifier(name) => {
            dependencies.add(name, DependencyKind::Value);
            node.set(Node::new(token.loc, NodeKind::Global(name)));
        }
        TokenKind::Open(Bracket::Round) => todo!(),
        _ => {
            global.error(token.loc, format!("Expected type, got {:?}", token.kind));
            return Err(());
        }
    }

    Ok(true)
}
