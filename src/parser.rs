pub mod ast;
mod context;
mod lexer;
mod token_stream;

use crate::errors::ErrorCtx;
use crate::locals::Local;
use crate::operators::{AccessOp, BinaryOp};
use ast::{Node, NodeKind};
use bump_tree::Tree;
use context::Context;
use lexer::{Bracket, Keyword, Literal, TokenKind};
use ustr::Ustr;

pub type Ast = Tree<Node>;
type NodeBuilder<'a> = bump_tree::NodeBuilder<'a, Node>;

pub fn process_string(errors: &mut ErrorCtx, file: Ustr, string: &str) -> Result<Ast, ()> {
    let tokens = lexer::process_string(errors, file, string)?;

    let mut ast = Ast::new();
    expression(&mut Context::new(errors, tokens), ast.builder())?;
    ast.set_root();

    Ok(ast)
}

fn expression(ctx: &mut Context<'_>, mut node: NodeBuilder<'_>) -> Result<(), ()> {
    value(ctx, node.arg())?;

    let mut old_op: Option<BinaryOp> = None;
    while let Some((loc, op, meta_data)) = ctx.tokens.try_consume_operator_with_metadata() {
        if !meta_data.cleared_operator_string {
            ctx.errors.warning(
                loc,
                "Ambiguous operator separation, please insert a space to clearly indicate \
                where the binary operator ends and the unary operators begin"
                    .to_string(),
            );
        }

        if old_op.unwrap_or(op).precedence() != op.precedence() {
            ctx.error(
                loc,
                "Only operators with the same precedence can be used after one another".to_string(),
            );
            return Err(());
        }

        value(ctx, node.arg())?;
        node.collapse(Node::new(loc, NodeKind::Binary(op)), 2);
        old_op = Some(op);
    }

    node.into_arg();
    Ok(())
}

/// A value allows for unary operators and member accesses or function insertions.
/// However, unary operators are only allowed before the accesses.
fn value(ctx: &mut Context<'_>, mut node: NodeBuilder<'_>) -> Result<(), ()> {
    if let Some((loc, op)) = ctx.tokens.try_consume_operator() {
        value(ctx, node.arg())?;
        node.set(Node::new(loc, NodeKind::Unary(op)));
        node.validate();
    } else {
        member_value(ctx, node)?;
    }

    Ok(())
}

/// A member value only allows for member accesses or function insertions. It does not
/// allow for unary operators.
fn member_value(ctx: &mut Context<'_>, mut node: NodeBuilder<'_>) -> Result<(), ()> {
    atom_value(ctx, node.arg())?;

    while let Some((loc, op)) = ctx.tokens.try_consume_operator() {
        match op {
            AccessOp::Member => {
                let token = ctx.tokens.expect_next(ctx.errors)?;
                if let TokenKind::Identifier(name) = token.kind {
                    node.collapse(Node::new(token.loc, NodeKind::Member(name)), 1);
                } else {
                    ctx.error(token.loc, "Expected identifier".to_string());
                }
            }
            AccessOp::FunctionInsert => {
                member_value(ctx, node.arg())?;
                node.collapse(Node::new(loc, NodeKind::FunctionInsert), 2);
            }
        }
    }

    node.into_arg();
    Ok(())
}

/// A value without unary operators, member accesses, or anything like that.
fn atom_value(ctx: &mut Context<'_>, mut node: NodeBuilder<'_>) -> Result<(), ()> {
    let token = ctx.tokens.expect_next(ctx.errors)?;
    match token.kind {
        TokenKind::Identifier(name) => {
            if let Some(local_id) = ctx.get_local(name) {
                node.set(Node::new(token.loc, NodeKind::Local(local_id)));
                node.validate();
            } else {
                ctx.error(
                    token.loc,
                    "Global variables are not supported yet".to_string(),
                );
                return Err(());
            }
        }

        TokenKind::Literal(Literal::Int(num)) => node.set(Node::new(token.loc, NodeKind::Int(num))),

        TokenKind::Keyword(Keyword::Let) => {
            let token = ctx.tokens.expect_next(ctx.errors)?;
            if let TokenKind::Identifier(name) = token.kind {
                let id = ctx.insert_local(Local {
                    loc: token.loc,
                    name,
                });

                ctx.tokens.try_consume_operator_string("=").ok_or_else(|| {
                    ctx.error(token.loc, "Expected '=' after identifier".into());
                })?;

                expression(ctx, node.arg())?;

                node.set(Node::new(token.loc, NodeKind::Declare(id)));
                node.validate();
            } else {
                ctx.error(token.loc, "Expected identifier".to_string());
                return Err(());
            }
        }

        TokenKind::Keyword(Keyword::Defer) => {
            let mut ast = Ast::new();
            expression(ctx, ast.builder())?;
            ast.set_root();
            ctx.push_defer(ast);

            node.set(Node::new(token.loc, NodeKind::Empty));
            node.validate();
        }

        TokenKind::Open(Bracket::Round) => {
            expression(ctx, node)?;
            ctx.tokens
                .expect_next_is(ctx.errors, &TokenKind::Close(Bracket::Round))?;
        }

        TokenKind::Open(Bracket::Curly) => {
            node.set(Node::new(token.loc, NodeKind::Block));
            let scope_boundary = ctx.push_scope_boundary();

            while !ctx
                .tokens
                .try_consume(ctx.errors, &TokenKind::Close(Bracket::Curly))?
            {
                expression(ctx, node.arg())?;
                ctx.tokens
                    .expect_next_is(ctx.errors, &TokenKind::SemiColon)?;
            }

            // Insert deferred definitions.
            for deferred in ctx.defers_to(scope_boundary) {
                node.arg().set_cloned(&deferred.root().unwrap());
            }

            ctx.pop_scope_boundary();
            node.validate();
        }

        _ => {
            ctx.error(
                token.loc,
                format!("Unexpected token '{:?}', expected value", token.kind),
            );
            return Err(());
        }
    }
    Ok(())
}
