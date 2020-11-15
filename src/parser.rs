pub mod ast;
mod context;
mod lexer;
mod token_stream;

use crate::errors::ErrorCtx;
use crate::locals::Local;
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

    if let Some((loc, op)) = ctx.tokens.try_consume_binary() {
        value(ctx, node.arg())?;
        node.set(Node::new(loc, NodeKind::Binary(op)));
        node.validate();
    } else {
        node.into_arg();
    }

    Ok(())
}

/// A value allows for unary operators and member accesses or function insertions.
/// However, unary operators are only allowed before the accesses.
fn value(ctx: &mut Context<'_>, mut node: NodeBuilder<'_>) -> Result<(), ()> {
    if let Some((loc, op)) = ctx.tokens.try_consume_unary() {
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

    if let Some((loc, op)) = ctx.tokens.try_consume_access_operator() {
        member_value(ctx, node.arg())?;
        node.set(Node::new(loc, NodeKind::Binary(op)));
        node.validate();
    } else {
        node.into_arg();
    }

    Ok(())
}

/// A value without unary operators, member accesses, or anything like that.
fn atom_value(ctx: &mut Context<'_>, mut node: NodeBuilder<'_>) -> Result<(), ()> {
    let token = ctx.tokens.expect_next(ctx.errors)?;
    match token.kind {
        TokenKind::Identifier(name) => {
            if let Some(local_id) = ctx.get_local(name) {
                node.set(Node::new(token.loc, NodeKind::Local(local_id)));
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

                ctx.tokens.try_consume_operator("=").ok_or_else(|| {
                    ctx.error(token.loc, "Expected '=' after identifier".into());
                })?;

                expression(ctx, node.arg())?;

                node.set(Node::new(token.loc, NodeKind::Declare(id)));
            } else {
                ctx.error(token.loc, "Expected identifier".to_string());
                return Err(());
            }
        }

        TokenKind::Keyword(Keyword::Defer) => {
            let mut ast = Ast::new();
            value(ctx, ast.builder())?;
            ast.set_root();
            ctx.push_defer(ast);

            node.set(Node::new(token.loc, NodeKind::Empty));
        }

        TokenKind::Open(Bracket::Curly) => {
            node.set(Node::new(token.loc, NodeKind::Block));
            let scope_boundary = ctx.push_scope_boundary();

            while !ctx
                .tokens
                .try_consume(ctx.errors, &TokenKind::Close(Bracket::Curly))?
            {
                value(ctx, node.arg())?;
                ctx.tokens
                    .expect_next_is(ctx.errors, &TokenKind::SemiColon)?;
            }

            // Insert deferred definitions.
            for deferred in ctx.defers_to(scope_boundary) {
                node.arg().set_cloned(&deferred.root().unwrap());
            }

            ctx.pop_scope_boundary();
        }

        _ => {
            ctx.error(
                token.loc,
                format!("Unexpected token '{:?}', expected value", token.kind),
            );
            return Err(());
        }
    }

    node.validate();
    Ok(())
}
