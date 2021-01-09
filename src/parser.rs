use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::locals::Local;
use crate::location::Location;
use crate::operators::BinaryOp;
use crate::program::{Program, ScopeId, Task};
use crate::self_buffer::{SelfBox, SelfBuffer, SelfTree};
use crate::types::TypeKind;
pub use ast::{Node, NodeKind};
use context::{DataContext, ImperativeContext};
use lexer::{Bracket, Keyword, Token, TokenKind};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use ustr::Ustr;

pub mod ast;
mod context;
mod lexer;
mod token_stream;

pub type Ast = SelfTree<Node>;
type NodeList = Vec<SelfBox<Node>>;
type NamedNodeList = Vec<(Ustr, SelfBox<Node>)>;

pub fn process_string(
    errors: &mut ErrorCtx,
    program: &Program,
    file: Ustr,
    string: &str,
    scope: ScopeId,
) -> Result<(), ()> {
    let mut tokens = lexer::process_string(errors, file, string)?;

    let mut context = DataContext::new(errors, program, &mut tokens, Path::new(&*file), scope);

    while let Some(token) = context.tokens.next() {
        match token.kind {
            TokenKind::Keyword(Keyword::Const) => constant(&mut context)?,
            TokenKind::Keyword(Keyword::Type) => {
                // This is a named type!

                let (loc, name) = context.tokens.expect_identifier(context.errors)?;

                let mut buffer = SelfBuffer::new();
                let mut dependencies = DependencyList::new();
                let mut imperative = ImperativeContext::new(&mut dependencies, false, &[]);
                imperative.evaluate_at_typing = true;
                let node = named_type(&mut context, &mut imperative, &mut buffer, loc, name)?;
                let tree = buffer.insert_root(node);

                let locals = imperative.locals;

                context
                    .tokens
                    .expect_next_is(context.errors, &TokenKind::SemiColon)?;

                let id = context.program.define_member(
                    context.errors,
                    token.loc,
                    context.scope,
                    name,
                )?;
                context
                    .program
                    .queue_task(dependencies, Task::TypeMember(id, locals, tree));
            }
            TokenKind::Keyword(Keyword::Library) => {
                let name = context.tokens.expect_next(context.errors)?;
                if let TokenKind::Literal(Literal::String(name)) = name.kind {
                    context
                        .tokens
                        .expect_next_is(context.errors, &TokenKind::SemiColon)?;

                    let path = offset_path(&context.program.arguments.lib_path, &name);

                    program.add_file_from_import(path, token.loc, context.scope);
                } else {
                    context.error(
                        name.loc,
                        "Expected string literal for file name".to_string(),
                    );
                    return Err(());
                }
            }
            TokenKind::Keyword(Keyword::Entry) => {
                let mut buffer = SelfBuffer::new();
                let mut dependencies = DependencyList::new();
                let mut imperative = ImperativeContext::new(&mut dependencies, false, &[]);
                let expr = expression(&mut context, &mut imperative, &mut buffer)?;
                let tree = buffer.insert_root(expr);

                context
                    .tokens
                    .expect_next_is(context.errors, &TokenKind::SemiColon)?;

                let locals = imperative.locals;

                let id = context.program.define_member(
                    context.errors,
                    token.loc,
                    context.scope,
                    "__entry_point".into(),
                )?;
                context
                    .program
                    .queue_task(dependencies, Task::TypeMember(id, locals, tree));

                let mut entry_point = context.program.entry_point.lock();
                if entry_point.is_some() {
                    context.error(
                        token.loc,
                        "There is already an entry point defined elsewhere".to_string(),
                    );
                    return Err(());
                }
                *entry_point = Some(id);
            }
            TokenKind::Keyword(Keyword::Import) => {
                let name = context.tokens.expect_next(context.errors)?;
                if let TokenKind::Literal(Literal::String(name)) = name.kind {
                    context
                        .tokens
                        .expect_next_is(context.errors, &TokenKind::SemiColon)?;

                    let mut path = context.path.to_path_buf();
                    path.pop();
                    let path = offset_path(&path, &name);

                    program.add_file_from_import(path, token.loc, context.scope);
                } else {
                    context.error(
                        name.loc,
                        "Expected string literal for file name".to_string(),
                    );
                    return Err(());
                }
            }
            _ => {
                context.error(token.loc, "Expected 'const' or 'import'".to_string());
                return Err(());
            }
        }
    }

    Ok(())
}

fn constant(global: &mut DataContext<'_>) -> Result<(), ()> {
    let token = global.tokens.expect_next(global.errors)?;
    if let TokenKind::Identifier(name) = token.kind {
        let polymorphic_arguments = maybe_parse_polymorphic_arguments(global)?;

        if global.tokens.try_consume_operator_string("=").is_none() {
            global.error(token.loc, "Expected '=' after const".to_string());
            return Err(());
        }

        let mut buffer = SelfBuffer::new();

        let mut dependencies = DependencyList::new();
        let mut imperative =
            ImperativeContext::new(&mut dependencies, false, &polymorphic_arguments);
        let expr = expression(global, &mut imperative, &mut buffer)?;
        let tree = buffer.insert_root(expr);

        let locals = imperative.locals;

        if polymorphic_arguments.is_empty() {
            let id = global
                .program
                .define_member(global.errors, token.loc, global.scope, name)?;
            global
                .program
                .queue_task(dependencies, Task::TypeMember(id, locals, tree));
        } else {
            let id = global.program.define_polymorphic_member(
                global.errors,
                token.loc,
                global.scope,
                name,
                locals,
                tree,
                polymorphic_arguments.len(),
            )?;
            global.program.queue_task(
                dependencies.clone(),
                Task::FlagPolyMember(id, MemberDep::Type, dependencies),
            );
        }

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
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut SelfBuffer,
) -> Result<Node, ()> {
    let mut expr = value(global, imperative, buffer)?;

    let mut old_op: Option<BinaryOp> = None;
    let mut is_first_iteration = false;
    while let Some((loc, op, meta_data)) = global.tokens.try_consume_operator_with_metadata() {
        if is_first_iteration {
            if expr.has_to_be_alone() {
                global
                    .errors
                    .error(expr.loc, "Parsing ambiguity, this is a value that contains another expression, hence it is required that you put it inside of parenthesees if you want to use it as an operand.".to_string());
                return Err(());
            }

            is_first_iteration = false;
        }

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

        let right = value(global, imperative, buffer)?;
        if right.has_to_be_alone() {
            global
                .errors
                .error(right.loc, "Parsing ambiguity, this is a value that contains another expression, hence it is required that you put it inside of parenthesees if you want to use it as an operand.".to_string());
            return Err(());
        }
        expr = Node::new(
            loc,
            NodeKind::Binary {
                op,
                left: buffer.insert(expr),
                right: buffer.insert(right),
            },
        );
        old_op = Some(op);
    }

    if let Some(loc) = global.tokens.try_consume_operator_string(":") {
        let type_bound = type_(global, imperative, buffer)?;
        Ok(Node::new(
            loc,
            NodeKind::TypeBound {
                value: buffer.insert(expr),
                bound: buffer.insert(type_bound),
            },
        ))
    } else {
        Ok(expr)
    }
}

fn named_type(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut SelfBuffer,
    loc: Location,
    name: Ustr,
) -> Result<Node, ()> {
    global
        .tokens
        .expect_next_is(global.errors, &TokenKind::Open(Bracket::Curly))?;

    let mut fields = Vec::new();
    let mut aliases = Vec::new();
    while !global.tokens.try_consume(&TokenKind::Close(Bracket::Curly)) {
        let token = global.tokens.expect_next(global.errors)?;
        match token.kind {
            TokenKind::Keyword(Keyword::Alias) => {
                let (_, name) = global.tokens.expect_identifier(global.errors)?;
                if global.tokens.try_consume_operator_string("=").is_none() {
                    global.error(global.tokens.loc(), "Expected '=' for alias".to_string());
                    return Err(());
                }

                let first = global.tokens.expect_identifier(global.errors)?;
                let mut fields = vec![first];
                while global.tokens.try_consume_operator_string(".").is_some() {
                    fields.push(global.tokens.expect_identifier(global.errors)?);
                }

                global
                    .tokens
                    .expect_next_is(global.errors, &TokenKind::SemiColon)?;
                aliases.push((name, fields));
            }
            TokenKind::Identifier(name) => {
                if global.tokens.try_consume_operator_string(":").is_none() {
                    global.error(
                        global.tokens.loc(),
                        "Expected ':' for field type".to_string(),
                    );
                    return Err(());
                }

                let type_ = type_(global, imperative, buffer)?;
                global
                    .tokens
                    .expect_next_is(global.errors, &TokenKind::SemiColon)?;

                fields.push((name, buffer.insert(type_)));
            }
            _ => {
                global.error(token.loc, "Expected field or alias".to_string());
                return Err(());
            }
        }
    }

    Ok(Node::new(
        loc,
        NodeKind::NamedType {
            name,
            fields,
            aliases,
        },
    ))
}

fn type_(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut SelfBuffer,
) -> Result<Node, ()> {
    let token = global.tokens.expect_peek(global.errors)?;
    let loc = token.loc;
    match token.kind {
        TokenKind::Identifier(name) => {
            global.tokens.next();

            let polymorphic_arguments =
                parse_passed_polymorphic_arguments(global, imperative, buffer)?;

            imperative.dependencies.add(
                loc,
                DepKind::MemberByName(global.scope, name, MemberDep::ValueAndCallableIfFunction),
            );
            Ok(Node::new(
                loc,
                NodeKind::GlobalForTyping(global.scope, name, polymorphic_arguments),
            ))
        }
        TokenKind::Open(Bracket::Curly) => {
            global.tokens.next();
            let mut fields = Vec::new();
            loop {
                if global.tokens.try_consume(&TokenKind::Close(Bracket::Curly)) {
                    break;
                }

                let identifier_token = global.tokens.expect_next(global.errors)?;
                let name = if let TokenKind::Identifier(name) = identifier_token.kind {
                    name
                } else {
                    global.error(identifier_token.loc, "Expected identifier".to_string());
                    return Err(());
                };

                if global.tokens.try_consume_operator_string(":").is_none() {
                    global.error(
                        global.tokens.loc(),
                        "Expected ':' for field type".to_string(),
                    );
                    return Err(());
                }

                let field_type = type_(global, imperative, buffer)?;
                fields.push((name, buffer.insert(field_type)));

                let token = global.tokens.expect_next(global.errors)?;
                match token.kind {
                    TokenKind::Close(Bracket::Curly) => break,
                    TokenKind::SemiColon => {}
                    _ => {
                        global.error(token.loc, "Expected ';' or ')'".to_string());
                        return Err(());
                    }
                }
            }

            Ok(Node::new(loc, NodeKind::StructType { fields }))
        }
        TokenKind::Open(Bracket::Square) => {
            global.tokens.next();
            match global.tokens.expect_peek(global.errors)?.kind {
                TokenKind::Close(Bracket::Square) => {
                    global.tokens.next();

                    if global.tokens.try_consume(&TokenKind::Keyword(Keyword::Any)) {
                        Ok(Node::new(
                            loc,
                            NodeKind::LiteralType(TypeKind::AnyBuffer.into()),
                        ))
                    } else {
                        let inner = type_(global, imperative, buffer)?;
                        Ok(Node::new(loc, NodeKind::BufferType(buffer.insert(inner))))
                    }
                }
                _ => {
                    let old_evaluate_at_typing = imperative.evaluate_at_typing;
                    imperative.evaluate_at_typing = true;
                    let len = expression(global, imperative, buffer)?;
                    global
                        .tokens
                        .expect_next_is(global.errors, &TokenKind::Close(Bracket::Square))?;
                    imperative.evaluate_at_typing = old_evaluate_at_typing;
                    let inner = type_(global, imperative, buffer)?;

                    Ok(Node::new(
                        loc,
                        NodeKind::ArrayType {
                            len: buffer.insert(len),
                            members: buffer.insert(inner),
                        },
                    ))
                }
            }
        }
        TokenKind::Open(Bracket::Round) => {
            global.tokens.next();
            if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
                Ok(Node::new(
                    loc,
                    NodeKind::LiteralType(TypeKind::Empty.into()),
                ))
            } else {
                let inner = type_(global, imperative, buffer)?;
                global
                    .tokens
                    .expect_next_is(global.errors, &TokenKind::Close(Bracket::Round))?;
                Ok(inner)
            }
        }
        TokenKind::Keyword(Keyword::Function) => {
            global.tokens.next();
            function_type(global, imperative, loc, buffer)
        }
        TokenKind::Keyword(Keyword::Bool) => {
            global.tokens.next();
            Ok(Node::new(loc, NodeKind::LiteralType(TypeKind::Bool.into())))
        }
        TokenKind::Type(type_) => {
            global.tokens.next();
            Ok(Node::new(loc, NodeKind::LiteralType(type_)))
        }
        TokenKind::PrimitiveInt(type_) => {
            global.tokens.next();
            Ok(Node::new(loc, NodeKind::LiteralType(type_.into())))
        }
        _ => {
            if global.tokens.try_consume_operator_string("&").is_some() {
                if global.tokens.try_consume(&TokenKind::Keyword(Keyword::Any)) {
                    Ok(Node::new(loc, NodeKind::LiteralType(TypeKind::Any.into())))
                } else {
                    let inner = type_(global, imperative, buffer)?;
                    Ok(Node::new(
                        loc,
                        NodeKind::ReferenceType(buffer.insert(inner)),
                    ))
                }
            } else {
                global.error(
                    loc,
                    "Unexpected token, expected type expression".to_string(),
                );
                Err(())
            }
        }
    }
}

/// A value
fn value(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut SelfBuffer,
) -> Result<Node, ()> {
    let mut unary_operators = Vec::new();
    while let Some((loc, op)) = global.tokens.try_consume_operator() {
        unary_operators.push((loc, op));
    }

    let token = global.tokens.expect_next(global.errors)?;
    let mut value = match token.kind {
        TokenKind::Identifier(name) => {
            let polymorphic_arguments =
                parse_passed_polymorphic_arguments(global, imperative, buffer)?;

            if let Some(local_id) = imperative.get_local(name) {
                if !polymorphic_arguments.is_empty() {
                    global.error(
                        token.loc,
                        "Cannot give a local polymorphic arguments".to_string(),
                    );
                    return Err(());
                }
                imperative.locals.get_mut(local_id).num_uses += 1;
                Node::new(token.loc, NodeKind::Local(local_id))
            } else if let Some(index) = imperative
                .poly_args
                .iter()
                .position(|(_, arg)| *arg == name)
            {
                Node::new(token.loc, NodeKind::PolymorphicArgument(index))
            } else if imperative.evaluate_at_typing {
                imperative.dependencies.add(
                    token.loc,
                    DepKind::MemberByName(
                        global.scope,
                        name,
                        MemberDep::ValueAndCallableIfFunction,
                    ),
                );
                Node::new(
                    token.loc,
                    NodeKind::GlobalForTyping(global.scope, name, polymorphic_arguments),
                )
            } else {
                imperative.dependencies.add(
                    token.loc,
                    DepKind::MemberByName(global.scope, name, MemberDep::Type),
                );
                Node::new(
                    token.loc,
                    NodeKind::Global(global.scope, name, polymorphic_arguments),
                )
            }
        }
        TokenKind::Literal(literal) => Node::new(token.loc, NodeKind::Literal(literal)),
        TokenKind::Keyword(Keyword::BuiltinFunction) => {
            use crate::program::BuiltinFunction;

            let (name_loc, name) = global.tokens.expect_identifier(global.errors)?;

            let builtin_kind = match name.as_str() {
                "mem_copy" => BuiltinFunction::MemCopy,
                "mem_copy_nonoverlapping" => BuiltinFunction::MemCopyNonOverlapping,
                "alloc" => BuiltinFunction::Alloc,
                "dealloc" => BuiltinFunction::Dealloc,
                "stdout_write" => BuiltinFunction::StdoutWrite,
                "stdout_flush" => BuiltinFunction::StdoutFlush,
                "stdin_get_line" => BuiltinFunction::StdinGetLine,
                _ => {
                    global.error(
                        name_loc,
                        format!("'{}' doesn't correspond to any built in function", name),
                    );
                    return Err(());
                }
            };

            Node::new(token.loc, NodeKind::BuiltinFunction(builtin_kind))
        }
        TokenKind::Keyword(Keyword::Const) => {
            let mut sub_ctx = ImperativeContext::new(
                imperative.dependencies,
                imperative.evaluate_at_typing,
                imperative.poly_args,
            );
            sub_ctx.in_const_expression = true;
            let inner = expression(global, &mut sub_ctx, buffer)?;

            if imperative.evaluate_at_typing {
                Node::new(
                    token.loc,
                    NodeKind::ConstAtTyping {
                        locals: sub_ctx.locals,
                        inner: buffer.insert(inner),
                    },
                )
            } else {
                Node::new(
                    token.loc,
                    NodeKind::ConstAtEvaluation {
                        locals: sub_ctx.locals,
                        inner: buffer.insert(inner),
                    },
                )
            }
        }
        TokenKind::Keyword(Keyword::Type) => {
            let t = type_(global, imperative, buffer)?;
            Node::new(token.loc, NodeKind::TypeAsValue(buffer.insert(t)))
        }
        TokenKind::Keyword(Keyword::Break) => {
            let id = if global.tokens.try_consume(&TokenKind::SingleQuote) {
                let (loc, label_name) = global.tokens.expect_identifier(global.errors)?;

                match imperative.get_label(label_name) {
                    Some(id) => id,
                    None => {
                        global.error(loc, format!("There is no label called '{}'", label_name));
                        return Err(());
                    }
                }
            } else if let Some(label) = imperative.last_default_label() {
                label
            } else {
                global.error(
                    token.loc,
                    "There is no default label to break to".to_string(),
                );
                return Err(());
            };

            let num_defer_deduplications = imperative.locals.get_label(id).num_defers;

            let value = if let Some(&Token {
                loc,
                kind: TokenKind::SemiColon,
            }) = global.tokens.peek()
            {
                Node::new(loc, NodeKind::Empty)
            } else {
                expression(global, imperative, buffer)?
            };

            let label_mut = imperative.locals.get_label_mut(id);
            if label_mut.first_break_location.is_none() {
                label_mut.first_break_location = Some(value.loc);
            }

            Node::new(
                token.loc,
                NodeKind::Break {
                    label: id,
                    num_defer_deduplications,
                    value: buffer.insert(value),
                },
            )
        }
        TokenKind::Keyword(Keyword::For) => {
            imperative.push_scope_boundary();

            let label = parse_default_label(global, imperative)?;

            let iterator = if let Some(Token {
                kind: TokenKind::Keyword(Keyword::In),
                ..
            }) = global.tokens.peek_nth(1)
            {
                let (name_loc, name) = global.tokens.expect_identifier(global.errors)?;
                global.tokens.next();

                imperative.insert_local(Local::new(name_loc, name))
            } else {
                imperative.insert_local(Local::new(token.loc, "_it".into()))
            };

            let iteration_var = imperative.insert_local(Local::new(token.loc, "_iters".into()));

            let iterating = expression(global, imperative, buffer)?;
            let body = expression(global, imperative, buffer)?;

            imperative.pop_default_label();
            imperative.pop_scope_boundary();

            let else_body = if global
                .tokens
                .try_consume(&TokenKind::Keyword(Keyword::Else))
            {
                let else_body = expression(global, imperative, buffer)?;
                Some(buffer.insert(else_body))
            } else {
                None
            };

            Node::new(
                token.loc,
                NodeKind::For {
                    iterator,
                    iteration_var,
                    iterating: buffer.insert(iterating),
                    body: buffer.insert(body),
                    label,
                    else_body,
                },
            )
        }
        TokenKind::Keyword(Keyword::While) => {
            imperative.push_scope_boundary();
            let label = parse_default_label(global, imperative)?;

            let iteration_var = imperative.insert_local(Local::new(token.loc, "_iters".into()));

            let condition = expression(global, imperative, buffer)?;
            let body = expression(global, imperative, buffer)?;

            imperative.pop_default_label();
            imperative.pop_scope_boundary();

            let else_body = if global
                .tokens
                .try_consume(&TokenKind::Keyword(Keyword::Else))
            {
                let else_body = expression(global, imperative, buffer)?;
                Some(buffer.insert(else_body))
            } else {
                None
            };

            Node::new(
                token.loc,
                NodeKind::While {
                    condition: buffer.insert(condition),
                    iteration_var,
                    body: buffer.insert(body),
                    label,
                    else_body,
                },
            )
        }
        TokenKind::Keyword(Keyword::If) => {
            let condition = expression(global, imperative, buffer)?;
            let true_body = expression(global, imperative, buffer)?;

            let false_body = if global
                .tokens
                .try_consume(&TokenKind::Keyword(Keyword::Else))
            {
                Some(expression(global, imperative, buffer)?)
            } else {
                None
            };

            Node::new(
                token.loc,
                NodeKind::If {
                    condition: buffer.insert(condition),
                    true_body: buffer.insert(true_body),
                    false_body: false_body.map(|v| buffer.insert(v)),
                },
            )
        }
        TokenKind::Keyword(Keyword::Uninit) => Node::new(token.loc, NodeKind::Uninit),
        TokenKind::Keyword(Keyword::Zeroed) => Node::new(token.loc, NodeKind::Zeroed),
        TokenKind::Keyword(Keyword::Function) => {
            function_declaration(global, imperative, buffer, token.loc)?
        }
        TokenKind::Keyword(Keyword::BitCast) => {
            let value = value(global, imperative, buffer)?;
            Node::new(
                token.loc,
                NodeKind::BitCast {
                    value: buffer.insert(value),
                },
            )
        }
        TokenKind::Open(Bracket::Square) => {
            let mut args = Vec::new();
            loop {
                if global
                    .tokens
                    .try_consume(&TokenKind::Close(Bracket::Square))
                {
                    break;
                }

                let expr = expression(global, imperative, buffer)?;
                args.push(buffer.insert(expr));

                let token = global.tokens.expect_next(global.errors)?;
                match token.kind {
                    TokenKind::Close(Bracket::Square) => break,
                    TokenKind::Comma => {}
                    _ => {
                        global.error(token.loc, "Expected either ',' or ']'".to_string());
                        return Err(());
                    }
                }
            }

            Node::new(token.loc, NodeKind::ArrayLiteral(args))
        }
        TokenKind::Open(Bracket::Round) => {
            let expr = expression(global, imperative, buffer)?;

            global
                .tokens
                .expect_next_is(global.errors, &TokenKind::Close(Bracket::Round))?;

            Node::new(token.loc, NodeKind::Parenthesis(buffer.insert(expr)))
        }

        TokenKind::Open(Bracket::Curly) => {
            imperative.push_scope_boundary();

            let label = maybe_parse_label(global, imperative)?;

            let mut contents = Vec::new();
            loop {
                if let Some(loc) = global
                    .tokens
                    .try_consume_with_data(&TokenKind::Close(Bracket::Curly))
                {
                    contents.push(buffer.insert(Node::new(loc, NodeKind::Empty)));
                    break;
                }

                let peek_token = global.tokens.expect_peek(global.errors)?;
                let loc = peek_token.loc;
                match peek_token.kind {
                    TokenKind::Keyword(Keyword::Defer) => {
                        global.tokens.next();

                        let deferring = expression(global, imperative, buffer)?;
                        let defer = Node::new(
                            loc,
                            NodeKind::Defer {
                                deferring: buffer.insert(deferring),
                            },
                        );
                        contents.push(buffer.insert(defer));

                        imperative.defer_depth += 1;

                        if let Some(label) = label {
                            imperative.locals.get_label_mut(label).num_defers += 1;
                        }
                    }
                    TokenKind::Keyword(Keyword::Let) => {
                        global.tokens.next();
                        let token = global.tokens.expect_next(global.errors)?;
                        if let TokenKind::Identifier(name) = token.kind {
                            global
                                .tokens
                                .try_consume_operator_string("=")
                                .ok_or_else(|| {
                                    global.error(token.loc, "Expected '=' after identifier".into());
                                })?;

                            let value = expression(global, imperative, buffer)?;

                            let id = imperative.insert_local(Local::new(token.loc, name));

                            let declaration = Node::new(
                                token.loc,
                                NodeKind::Declare {
                                    local: id,
                                    value: buffer.insert(value),
                                },
                            );

                            contents.push(buffer.insert(declaration));
                        } else {
                            global.error(token.loc, "Expected identifier".to_string());
                            return Err(());
                        }
                    }
                    _ => {
                        let inner = expression(global, imperative, buffer)?;

                        if let Some(loc) = global.tokens.try_consume_operator_string("=") {
                            let rvalue = expression(global, imperative, buffer)?;
                            let assignment = Node::new(
                                loc,
                                NodeKind::Assign {
                                    lvalue: buffer.insert(inner),
                                    rvalue: buffer.insert(rvalue),
                                },
                            );
                            contents.push(buffer.insert(assignment));
                        } else {
                            contents.push(buffer.insert(inner));
                        }
                    }
                }

                let token = global.tokens.expect_next(global.errors)?;
                match token.kind {
                    TokenKind::SemiColon => {}
                    TokenKind::Close(Bracket::Curly) => break,
                    _ => {
                        global.error(
                            token.loc,
                            "Expected ';' or '}', or a '=' for assignment".to_string(),
                        );
                        return Err(());
                    }
                }
            }

            imperative.pop_scope_boundary();
            Node::new(token.loc, NodeKind::Block { label, contents })
        }

        _ => {
            global.error(
                token.loc,
                format!("Unexpected token '{:?}', expected value", token.kind),
            );
            return Err(());
        }
    };

    while let Some(&Token { ref kind, loc, .. }) = global.tokens.peek() {
        match kind {
            TokenKind::Operator(string) if string.as_str() == "." => {
                global.tokens.next();

                let (_, name) = global.tokens.expect_identifier(global.errors)?;
                value = Node::new(
                    loc,
                    NodeKind::Member {
                        of: buffer.insert(value),
                        name,
                    },
                );
            }
            TokenKind::Open(Bracket::Round) => {
                global.tokens.next();

                let (args, named_args) = function_arguments(global, imperative, buffer)?;

                value = Node::new(
                    loc,
                    NodeKind::FunctionCall {
                        calling: buffer.insert(value),
                        args,
                        named_args,
                    },
                );
            }
            _ => break,
        }
    }

    while let Some((loc, op)) = unary_operators.pop() {
        value = Node::new(
            loc,
            NodeKind::Unary {
                operand: buffer.insert(value),
                op,
            },
        );
    }

    Ok(value)
}

fn function_type(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    loc: Location,
    buffer: &mut SelfBuffer,
) -> Result<Node, ()> {
    // We start with a list of arguments.
    global
        .tokens
        .expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;

    let mut args = Vec::new();
    loop {
        if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
            break;
        }

        let arg_type = type_(global, imperative, buffer)?;
        args.push(buffer.insert(arg_type));

        let token = global.tokens.expect_next(global.errors)?;
        match token.kind {
            TokenKind::Close(Bracket::Round) => break,
            TokenKind::Comma => {}
            _ => {
                global.error(token.loc, "Expected ',' or ')'".to_string());
                return Err(());
            }
        }
    }

    let returns = if global.tokens.try_consume_operator_string("->").is_some() {
        type_(global, imperative, buffer)?
    } else {
        Node::new(loc, NodeKind::LiteralType(TypeKind::Empty.into()))
    };

    Ok(Node::new(
        loc,
        NodeKind::FunctionType {
            args,
            returns: buffer.insert(returns),
        },
    ))
}

fn function_arguments(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut SelfBuffer,
) -> Result<(NodeList, NamedNodeList), ()> {
    let mut args = Vec::new();
    let mut named_args = Vec::new();
    loop {
        if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
            break;
        }

        match (
            global.tokens.peek().map(|t| &t.kind),
            global.tokens.peek_nth(1).map(|t| &t.kind),
        ) {
            (Some(&TokenKind::Identifier(name)), Some(TokenKind::Operator(operator)))
                if operator.starts_with('=') =>
            {
                // Named argument
                global.tokens.next();
                global.tokens.try_consume_operator_string("=").unwrap();

                let arg = expression(global, imperative, buffer)?;

                named_args.push((name, buffer.insert(arg)));
            }
            _ => {
                let arg = expression(global, imperative, buffer)?;

                if !named_args.is_empty() {
                    global.error(
                        arg.loc,
                        "You cannot have unnamed arguments after named arguments".to_string(),
                    );
                    return Err(());
                }

                args.push(buffer.insert(arg));
            }
        }

        let token = global.tokens.expect_next(global.errors)?;
        match token.kind {
            TokenKind::Close(Bracket::Round) => break,
            TokenKind::Comma => {}
            _ => {
                global.error(token.loc, "Expected ',' or ')'".into());
                return Err(());
            }
        }
    }

    Ok((args, named_args))
}

/// Parses a function declaration, although doesn't expect the 'fn' keyword to be included because
/// that keyword was what triggered this function to be called in the first place.
fn function_declaration(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut SelfBuffer,
    loc: Location,
) -> Result<Node, ()> {
    global
        .tokens
        .expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;

    let mut body_deps = DependencyList::new();
    let mut sub_imperative = ImperativeContext::new(&mut body_deps, false, imperative.poly_args);

    let mut args = Vec::new();
    let mut default_args = Vec::new();

    let old = imperative.evaluate_at_typing;
    imperative.evaluate_at_typing = true;
    loop {
        if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
            break;
        }

        if let Some(Token {
            loc,
            kind: TokenKind::Identifier(name),
            ..
        }) = global.tokens.next()
        {
            sub_imperative.insert_local(Local::new(loc, name));

            if global.tokens.try_consume_operator_string(":").is_some() {
                if !default_args.is_empty() {
                    global.error(
                        global.tokens.loc(),
                        "Cannot define non-default arguments after the first default argument"
                            .to_string(),
                    );
                    return Err(());
                }

                let arg_type = type_(global, imperative, buffer)?;
                args.push((name, buffer.insert(arg_type)));
            } else if global.tokens.try_consume_operator_string("=").is_some() {
                let arg_value = expression(global, imperative, buffer)?;
                default_args.push((name, buffer.insert(arg_value)));
            } else {
                global.error(
                    global.tokens.loc(),
                    "Expected ':' for argument type, or '=' for argument default value".to_string(),
                );
                return Err(());
            }
        } else {
            global.error(
                global.tokens.loc(),
                "Expected identifier for function argument name".to_string(),
            );
            return Err(());
        }

        let token = global.tokens.expect_next(global.errors)?;
        match token.kind {
            TokenKind::Close(Bracket::Round) => break,
            TokenKind::Comma => {}
            _ => {
                global.error(token.loc, "Expected ',' or ')'".into());
                return Err(());
            }
        }
    }

    imperative.evaluate_at_typing = old;

    let returns = if global.tokens.try_consume_operator_string("->").is_some() {
        type_(global, imperative, buffer)?
    } else {
        Node::new(
            global.tokens.loc(),
            NodeKind::LiteralType(TypeKind::Empty.into()),
        )
    };

    let mut body_buffer = SelfBuffer::new();
    let body = expression(global, &mut sub_imperative, &mut body_buffer)?;
    let body = Arc::new(body_buffer.insert_root(body));

    Ok(Node::new(
        loc,
        NodeKind::FunctionDeclaration {
            locals: sub_imperative.locals,
            args,
            default_args,
            returns: buffer.insert(returns),
            body_deps,
            body,
        },
    ))
}

// FIXME: The name of this is confusing af, just make it simple
fn parse_passed_polymorphic_arguments(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut SelfBuffer,
) -> Result<Vec<SelfBox<Node>>, ()> {
    let mut polymorphic_arguments = Vec::new();
    if global.tokens.try_consume(&TokenKind::Open(Bracket::Square)) {
        let old_evaluate_at_typing = imperative.evaluate_at_typing;
        imperative.evaluate_at_typing = true;
        loop {
            if global
                .tokens
                .try_consume(&TokenKind::Close(Bracket::Square))
            {
                break;
            }

            let arg = expression(global, imperative, buffer)?;
            polymorphic_arguments.push(buffer.insert(arg));

            let token = global.tokens.expect_next(global.errors)?;
            match token.kind {
                TokenKind::Close(Bracket::Square) => break,
                TokenKind::Comma => {}
                _ => {
                    global.error(token.loc, "Expected either ',' or ']'".to_string());
                    return Err(());
                }
            }
        }
        imperative.evaluate_at_typing = old_evaluate_at_typing;
    }
    Ok(polymorphic_arguments)
}

fn maybe_parse_polymorphic_arguments(
    global: &mut DataContext<'_>,
) -> Result<Vec<(Location, Ustr)>, ()> {
    let mut args = Vec::new();
    if global.tokens.try_consume(&TokenKind::Open(Bracket::Square)) {
        loop {
            if global
                .tokens
                .try_consume(&TokenKind::Close(Bracket::Square))
            {
                break;
            }

            let (loc, name) = global.tokens.expect_identifier(global.errors)?;
            args.push((loc, name));

            let token = global.tokens.expect_next(global.errors)?;
            match token.kind {
                TokenKind::Close(Bracket::Square) => break,
                TokenKind::Comma => {}
                _ => {
                    global.error(token.loc, "Expected either ',' or ']'".to_string());
                    return Err(());
                }
            }
        }
    }
    Ok(args)
}

fn parse_default_label(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
) -> Result<crate::locals::LabelId, ()> {
    let loc = global.tokens.loc();

    let name = if global.tokens.try_consume(&TokenKind::SingleQuote) {
        let (_, name) = global.tokens.expect_identifier(global.errors)?;
        Some(name)
    } else {
        None
    };

    let id = imperative.insert_default_label(
        name,
        crate::locals::Label {
            loc,
            defer_depth: imperative.defer_depth,
            first_break_location: None,
            num_defers: 0,
            type_: None,
            value: None,
            ir_labels: None,
        },
    );

    Ok(id)
}

fn maybe_parse_label(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
) -> Result<Option<crate::locals::LabelId>, ()> {
    if global.tokens.try_consume(&TokenKind::SingleQuote) {
        let (loc, name) = global.tokens.expect_identifier(global.errors)?;
        let id = imperative.insert_label(
            name,
            crate::locals::Label {
                loc,
                defer_depth: imperative.defer_depth,
                first_break_location: None,
                num_defers: 0,
                type_: None,
                value: None,
                ir_labels: None,
            },
        );
        Ok(Some(id))
    } else {
        Ok(None)
    }
}

fn offset_path(path: &Path, addition: &str) -> PathBuf {
    let mut path = path
        .canonicalize()
        .expect("TODO: Make an error message for not being able to canonicalize paths");

    for part in addition.split('/') {
        if part == ".." {
            path.pop();
        } else {
            path.push(part);
        }
    }

    path
}
