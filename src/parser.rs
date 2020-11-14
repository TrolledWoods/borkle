pub mod ast;
mod context;
mod lexer;
mod token_stream;

use crate::errors::ErrorCtx;
use crate::locals::Local;
use crate::tree::Tree;
use ast::{Node, NodeKind};
use context::Context;
use lexer::{Bracket, Keyword, Literal, TokenKind};
use ustr::Ustr;

pub type Ast = Tree<Node>;
type NodeBuilder<'a> = crate::tree::NodeBuilder<'a, Node>;

pub fn process_string(errors: &mut ErrorCtx, file: Ustr, string: &str) -> Result<Ast, ()> {
    let tokens = lexer::process_string(errors, file, string)?;

    let mut ast = Ast::new();
    value(&mut Context::new(errors, tokens), ast.builder())?;
    ast.set_root();

    Ok(ast)
}

fn value(ctx: &mut Context<'_>, mut node: NodeBuilder<'_>) -> Result<(), ()> {
    // Check for unary operator
    if let Some((loc, op)) = ctx.tokens.try_consume_unary() {
        value(ctx, node.arg())?;
        node.set(Node::new(loc, NodeKind::Unary(op)));
        node.validate();
    } else {
        atom_value(ctx, node)?;
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

                value(ctx, node.arg())?;

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
