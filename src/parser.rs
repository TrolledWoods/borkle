use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::locals::{Local, LocalVariables};
use crate::location::Location;
use crate::operators::{BinaryOp, Operator, UnaryOp};
use crate::program::{Program, ScopeId, Task};
use crate::types::{PtrPermits, Type, TypeKind};
pub use ast::{AstBuilder, Node, NodeId, NodeKind};
use context::{DataContext, ImperativeContext};
use lexer::{Bracket, Keyword, Token, TokenKind};
use std::path::{Path, PathBuf};
use ustr::Ustr;

pub mod ast;
mod context;
mod lexer;
mod token_stream;

pub type Ast = ast::Ast;
type NodeList = Vec<NodeId>;
type NamedNodeList = Vec<(Ustr, NodeId)>;

pub fn process_string(
    errors: &mut ErrorCtx,
    program: &Program,
    file: Ustr,
    string: &str,
    scope: ScopeId,
) -> Result<(), ()> {
    profile::profile!("process_string");

    let mut tokens = lexer::process_string(errors, file, string)?;

    let mut context = DataContext::new(errors, program, &mut tokens, Path::new(&*file), scope);

    while let Some(token) = context.tokens.next() {
        match token.kind {
            TokenKind::Keyword(Keyword::Const) => constant(&mut context)?,
            TokenKind::Keyword(Keyword::Type) => {
                // This is a named type!

                let (loc, name) = context.tokens.expect_identifier(context.errors)?;

                let mut buffer = AstBuilder::new();
                let mut dependencies = DependencyList::new();
                let mut locals = LocalVariables::new();
                let mut imperative =
                    ImperativeContext::new(&mut dependencies, &mut locals, false, &[]);
                imperative.evaluate_at_typing = true;
                let node = named_type(&mut context, &mut imperative, &mut buffer, loc, name)?;

                let tree = buffer.set_root(node);

                context
                    .tokens
                    .expect_next_is(context.errors, &TokenKind::SemiColon)?;

                let id = context.program.define_member(
                    context.errors,
                    token.loc,
                    context.scope,
                    name,
                )?;

                context.program.queue_task(
                    dependencies,
                    Task::TypeMember { member_id: id, locals, ast: tree },
                );
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
                let mut buffer = AstBuilder::new();
                let mut dependencies = DependencyList::new();
                let mut locals = LocalVariables::new();
                let mut imperative =
                    ImperativeContext::new(&mut dependencies, &mut locals, false, &[]);
                let expr = expression(&mut context, &mut imperative, &mut buffer)?;
                let tree = buffer.set_root(expr);

                context
                    .tokens
                    .expect_next_is(context.errors, &TokenKind::SemiColon)?;

                let id = context.program.define_member(
                    context.errors,
                    token.loc,
                    context.scope,
                    "__entry_point".into(),
                )?;
                context.program.queue_task(
                    dependencies,
                    Task::TypeMember { member_id: id, locals, ast: tree },
                );

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

        let mut buffer = AstBuilder::new();

        let mut dependencies = DependencyList::new();
        let mut locals = LocalVariables::new();
        let mut imperative = ImperativeContext::new(
            &mut dependencies,
            &mut locals,
            false,
            &polymorphic_arguments,
        );
        let expr = expression(global, &mut imperative, &mut buffer)?;
        let tree = buffer.set_root(expr);

        if polymorphic_arguments.is_empty() {
            let id = global
                .program
                .define_member(global.errors, token.loc, global.scope, name)?;
            global.program.queue_task(
                dependencies,
                Task::TypeMember { member_id: id, locals, ast: tree },
            );
        } else {
            let id = global.program.define_polymorphic_member(
                global.errors,
                token.loc,
                global.scope,
                name,
                polymorphic_arguments.len(),
            )?;
            global.program.queue_task(
                dependencies.clone(),
                Task::TypePolyMember {
                    member_id: id,
                    locals,
                    ast: tree,
                    dependencies,
                },
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
    buffer: &mut AstBuilder,
) -> Result<NodeId, ()> {
    let expr = expression_rec(global, imperative, buffer, 0)?;

    Ok(expr)
}

fn expression_rec(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut AstBuilder,
    precedence: usize,
) -> Result<NodeId, ()> {
    let mut expr = value(global, imperative, buffer)?;

    while let Some((loc, op)) = global
        .tokens
        .try_consume_operator_with_precedence(precedence)
    {
        // @Improvement: Reimplement `has_to_be_alone`

        if op == BinaryOp::TypeBound {
            let right = type_(global, imperative, buffer)?;
            expr = buffer.add(Node::new(
                loc,
                NodeKind::TypeBound {
                    value: expr,
                    bound: right,
                },
            ));
        } else {
            let right = expression_rec(global, imperative, buffer, op.precedence())?;
            expr = buffer.add(Node::new(
                loc,
                NodeKind::Binary {
                    op,
                    left: expr,
                    right: right,
                },
            ));
        }
    }

    Ok(expr)
}

fn named_type(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut AstBuilder,
    loc: Location,
    name: Ustr,
) -> Result<NodeId, ()> {
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

                fields.push((name, type_));
            }
            _ => {
                global.error(token.loc, "Expected field or alias".to_string());
                return Err(());
            }
        }
    }

    Ok(buffer.add(Node::new(
        loc,
        NodeKind::NamedType {
            name,
            fields,
            aliases,
        },
    )))
}

fn type_(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut AstBuilder,
) -> Result<NodeId, ()> {
    let token = global.tokens.expect_peek(global.errors)?;
    let loc = token.loc;
    match token.kind {
        TokenKind::Keyword(Keyword::TypeOf) => {
            global.tokens.next();

            // @TODO: We want to tell the parser about
            // the fact that we don't actually need the values of anything
            // in here, so that it doesn't fetch them unnecessarily
            let inner = value(global, imperative, buffer)?;

            Ok(buffer.add(Node::new(
                loc,
                NodeKind::TypeOf(inner),
            )))
        }
        TokenKind::Identifier(name) => {
            global.tokens.next();

            if let Some(index) = imperative
                .poly_args
                .iter()
                .position(|(_, arg)| *arg == name)
            {
                Ok(buffer.add(Node::new(loc, NodeKind::PolymorphicArgument(index))))
            } else {
                imperative.dependencies.add(
                    loc,
                    DepKind::MemberByName(
                        global.scope,
                        name,
                        MemberDep::ValueAndCallableIfFunction,
                    ),
                );
                Ok(buffer.add(Node::new(
                    loc,
                    NodeKind::GlobalForTyping(global.scope, name, Vec::new()),
                )))
            }
        }
        TokenKind::Keyword(Keyword::Underscore) => {
            global.tokens.next();

            Ok(buffer.add(Node::new(loc, NodeKind::ImplicitType)))
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
                fields.push((name, field_type));

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

            Ok(buffer.add(Node::new(loc, NodeKind::StructType { fields })))
        }
        TokenKind::Open(Bracket::Square) => {
            global.tokens.next();
            match global.tokens.expect_peek(global.errors)?.kind {
                TokenKind::Close(Bracket::Square) => {
                    global.tokens.next();

                    if global
                        .tokens
                        .try_consume(&TokenKind::Keyword(Keyword::Void))
                    {
                        Ok(buffer.add(Node::new(
                            loc,
                            NodeKind::LiteralType(TypeKind::VoidBuffer.into()),
                        )))
                    } else {
                        let permits = parse_pointer_permits(global);
                        let inner = type_(global, imperative, buffer)?;
                        Ok(buffer.add(Node::new(loc, NodeKind::BufferType(inner, permits))))
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

                    Ok(buffer.add(Node::new(
                        loc,
                        NodeKind::ArrayType {
                            len,
                            members: inner,
                        },
                    )))
                }
            }
        }
        TokenKind::Open(Bracket::Round) => {
            global.tokens.next();
            if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
                Ok(buffer.add(Node::new(
                    loc,
                    NodeKind::LiteralType(TypeKind::Empty.into()),
                )))
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
            Ok(buffer.add(Node::new(loc, NodeKind::LiteralType(TypeKind::Bool.into()))))
        }
        TokenKind::Type(type_) => {
            global.tokens.next();
            Ok(buffer.add(Node::new(loc, NodeKind::LiteralType(type_))))
        }
        TokenKind::PrimitiveInt(type_) => {
            global.tokens.next();
            Ok(buffer.add(Node::new(loc, NodeKind::LiteralType(type_.into()))))
        }
        _ => {
            if global.tokens.try_consume_operator_string("&").is_some() {
                let permits = parse_pointer_permits(global);

                if global
                    .tokens
                    .try_consume(&TokenKind::Keyword(Keyword::Void))
                {
                    // @TODO: This type should also have pointer permits
                    Ok(buffer.add(Node::new(
                        loc,
                        NodeKind::LiteralType(Type::new(TypeKind::VoidPtr)),
                    )))
                } else if global.tokens.try_consume(&TokenKind::Keyword(Keyword::Any)) {
                    // @TODO: This type should also have pointer permits
                    Ok(buffer.add(Node::new(
                        loc,
                        NodeKind::LiteralType(Type::new(TypeKind::AnyPtr)),
                    )))
                } else {
                    let inner = type_(global, imperative, buffer)?;
                    Ok(buffer.add(Node::new(loc, NodeKind::ReferenceType(inner, permits))))
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

fn value(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut AstBuilder,
) -> Result<NodeId, ()> {
    if let Some((loc, op)) = global.tokens.try_consume_operator() {
        if op == UnaryOp::Reference {
            let value = value(global, imperative, buffer)?;
            Ok(buffer.add(Node::new(loc, NodeKind::Reference(value))))
        } else {
            let value = value(global, imperative, buffer)?;
            Ok(buffer.add(Node::new(loc, NodeKind::Unary { operand: value, op })))
        }
    } else {
        value_without_unaries(global, imperative, buffer)
    }
}

/// A value
fn value_without_unaries(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut AstBuilder,
) -> Result<NodeId, ()> {
    let token = global.tokens.expect_next(global.errors)?;
    let mut value = match token.kind {
        TokenKind::Identifier(name) => {
            if let Some(local_id) = imperative.get_local(name) {
                let local = imperative.locals.get_mut(local_id);
                local.num_uses += 1;
                let id = buffer.add(Node::new(token.loc, NodeKind::Local(local_id)));
                local.uses.push(id);
                id
            } else if let Some(index) = imperative
                .poly_args
                .iter()
                .position(|(_, arg)| *arg == name)
            {
                buffer.add(Node::new(token.loc, NodeKind::PolymorphicArgument(index)))
            } else if imperative.evaluate_at_typing {
                imperative.dependencies.add(
                    token.loc,
                    DepKind::MemberByName(
                        global.scope,
                        name,
                        MemberDep::ValueAndCallableIfFunction,
                    ),
                );
                buffer.add(Node::new(
                    token.loc,
                    NodeKind::GlobalForTyping(global.scope, name, Vec::new()),
                ))
            } else {
                imperative.dependencies.add(
                    token.loc,
                    DepKind::MemberByName(global.scope, name, MemberDep::Type),
                );
                buffer.add(Node::new(
                    token.loc,
                    NodeKind::Global(global.scope, name, Vec::new()),
                ))
            }
        }
        TokenKind::Literal(literal) => buffer.add(Node::new(token.loc, NodeKind::Literal(literal))),
        TokenKind::Keyword(Keyword::BuiltinFunction) => {
            use crate::program::BuiltinFunction;

            let (name_loc, name) = global.tokens.expect_identifier(global.errors)?;

            let builtin_kind = match name.as_str() {
                "assert" => BuiltinFunction::Assert,
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

            buffer.add(Node::new(
                token.loc,
                NodeKind::BuiltinFunction(builtin_kind),
            ))
        }
        TokenKind::Keyword(Keyword::Const) => {
            // @TODO: Prevent cross-referencing of variable values here!!!!!!!!!!!
            // Could probably do it just by looking at what scope_id local reads/writes have,
            // as well as what scope_id the declarations of locals have. That should be all that's necessary....
            let old_in_const_expr = imperative.in_const_expression;
            imperative.in_const_expression = true;
            let inner = expression(global, imperative, buffer)?;
            imperative.in_const_expression = old_in_const_expr;

            if imperative.evaluate_at_typing {
                buffer.add(Node::new(token.loc, NodeKind::ConstAtTyping { inner }))
            } else {
                buffer.add(Node::new(token.loc, NodeKind::ConstAtEvaluation { inner }))
            }
        }
        TokenKind::Keyword(Keyword::SizeOf) => {
            let t = type_(global, imperative, buffer)?;
            buffer.add(Node::new(token.loc, NodeKind::SizeOf(t)))
        }
        TokenKind::Keyword(Keyword::Type) => {
            let t = type_(global, imperative, buffer)?;
            buffer.add(Node::new(token.loc, NodeKind::TypeAsValue(t)))
        }
        TokenKind::PrimitiveInt(type_) => {
            let type_node = buffer.add(Node::new(token.loc, NodeKind::LiteralType(type_.into())));
            buffer.add(Node::new(token.loc, NodeKind::TypeAsValue(type_node)))
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
                buffer.add(Node::new(loc, NodeKind::Empty))
            } else {
                expression(global, imperative, buffer)?
            };

            let label_mut = imperative.locals.get_label_mut(id);
            if label_mut.first_break_location.is_none() {
                label_mut.first_break_location = Some(buffer.get(value).loc);
            }

            buffer.add(Node::new(
                token.loc,
                NodeKind::Break {
                    label: id,
                    num_defer_deduplications,
                    value,
                },
            ))
        }
        TokenKind::Keyword(Keyword::For) => {
            imperative.push_scope_boundary();

            let label = parse_default_label(global, imperative)?;

            let iterator_local = if let Some(Token {
                kind: TokenKind::Keyword(Keyword::In),
                ..
            }) = global.tokens.peek_nth(1)
            {
                let (name_loc, name) = global.tokens.expect_identifier(global.errors)?;
                global.tokens.next();

                Local::new(name_loc, name)
            } else {
                Local::new(token.loc, "_it".into())
            };

            let iterating = expression(global, imperative, buffer)?;

            let iterator = imperative.insert_local(iterator_local);
            let iteration_var = imperative.insert_local(Local::new(token.loc, "_iters".into()));

            let body = expression(global, imperative, buffer)?;

            imperative.pop_default_label();
            imperative.pop_scope_boundary();

            let else_body = if global
                .tokens
                .try_consume(&TokenKind::Keyword(Keyword::Else))
            {
                let else_body = expression(global, imperative, buffer)?;
                Some(else_body)
            } else {
                None
            };

            buffer.add(Node::new(
                token.loc,
                NodeKind::For {
                    iterator,
                    iteration_var,
                    iterating,
                    body,
                    label,
                    else_body,
                },
            ))
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
                Some(else_body)
            } else {
                None
            };

            buffer.add(Node::new(
                token.loc,
                NodeKind::While {
                    condition,
                    iteration_var,
                    body,
                    label,
                    else_body,
                },
            ))
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

            buffer.add(Node::new(
                token.loc,
                NodeKind::If {
                    condition,
                    true_body,
                    false_body,
                },
            ))
        }
        TokenKind::Keyword(Keyword::Uninit) => buffer.add(Node::new(token.loc, NodeKind::Uninit)),
        TokenKind::Keyword(Keyword::Zeroed) => buffer.add(Node::new(token.loc, NodeKind::Zeroed)),
        TokenKind::Keyword(Keyword::Function) => {
            function_declaration(global, imperative, buffer, token.loc)?
        }
        TokenKind::Keyword(Keyword::Cast) => {
            let value = value(global, imperative, buffer)?;
            buffer.add(Node::new(token.loc, NodeKind::Cast { value }))
        }
        TokenKind::Keyword(Keyword::BitCast) => {
            let value = value(global, imperative, buffer)?;
            buffer.add(Node::new(token.loc, NodeKind::BitCast { value }))
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
                args.push(expr);

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

            buffer.add(Node::new(token.loc, NodeKind::ArrayLiteral(args)))
        }
        TokenKind::Open(Bracket::Round) => {
            let expr = expression(global, imperative, buffer)?;

            global
                .tokens
                .expect_next_is(global.errors, &TokenKind::Close(Bracket::Round))?;

            buffer.add(Node::new(token.loc, NodeKind::Parenthesis(expr)))
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
                    contents.push(buffer.add(Node::new(loc, NodeKind::Empty)));
                    break;
                }

                let peek_token = global.tokens.expect_peek(global.errors)?;
                let loc = peek_token.loc;
                match peek_token.kind {
                    TokenKind::Keyword(Keyword::Defer) => {
                        global.tokens.next();

                        let deferring = expression(global, imperative, buffer)?;
                        let defer = buffer.add(Node::new(loc, NodeKind::Defer { deferring }));
                        contents.push(defer);

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
                            let dummy_local_node =
                                buffer.add(Node::new(token.loc, NodeKind::Local(id)));
                            // @Cleanup: Remove this, not necessary anymore
                            imperative.locals.get_mut(id).uses.push(dummy_local_node);

                            let declaration = buffer.add(Node::new(
                                token.loc,
                                NodeKind::Declare {
                                    local: id,
                                    value,
                                    dummy_local_node,
                                },
                            ));

                            contents.push(declaration);
                        } else {
                            global.error(token.loc, "Expected identifier".to_string());
                            return Err(());
                        }
                    }
                    _ => {
                        let inner = expression(global, imperative, buffer)?;
                        contents.push(inner);
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
            buffer.add(Node::new(token.loc, NodeKind::Block { label, contents }))
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

                let token = global.tokens.expect_next(global.errors)?;
                match token.kind {
                    TokenKind::Identifier(name) => {
                        value = buffer.add(Node::new(loc, NodeKind::Member { of: value, name }));
                    }
                    TokenKind::Open(Bracket::Round) => {
                        let mut polymorphic_arguments = Vec::new();

                        let old_evaluate_at_typing = imperative.evaluate_at_typing;
                        imperative.evaluate_at_typing = true;
                        // @Cleanup: We should be able to deduplicate this code with function argument parsing...
                        loop {
                            if global
                                .tokens
                                .try_consume(&TokenKind::Close(Bracket::Round))
                            {
                                break;
                            }

                            let arg = expression(global, imperative, buffer)?;
                            polymorphic_arguments.push(arg);
                            buffer.get_mut(arg).parent = Some(value);

                            let token = global.tokens.expect_next(global.errors)?;
                            match token.kind {
                                TokenKind::Close(Bracket::Round) => break,
                                TokenKind::Comma => {}
                                _ => {
                                    global.error(token.loc, "Expected either ',' or ')'".to_string());
                                    return Err(());
                                }
                            }
                        }
                        imperative.evaluate_at_typing = old_evaluate_at_typing;

                        let prev = buffer.get_mut(value);
                        match prev.kind {
                            NodeKind::Global(scope, name, ref args) if args.is_empty() => {
                                prev.kind = NodeKind::Global(scope, name, polymorphic_arguments);
                            }
                            NodeKind::Global(_, _, _) => {
                                global.error(loc, "Cannot pass polymorphic arguments twice".to_string());
                                return Err(());
                            }
                            NodeKind::GlobalForTyping(scope, name, ref args) if args.is_empty() => {
                                prev.kind = NodeKind::GlobalForTyping(scope, name, polymorphic_arguments);
                            }
                            NodeKind::GlobalForTyping(_, _, _) => {
                                global.error(loc, "Cannot pass polymorphic arguments twice".to_string());
                                return Err(());
                            }
                            _ => {
                                global.error(loc, "Cannot pass polymorphic arguments to anything other than a global value".to_string());
                                return Err(());
                            },
                        }
                    }
                    _ => {
                        global.error(token.loc, "Expected either an identifier, or a generic argument list".to_string());
                        return Err(());
                    }
                }
            }
            TokenKind::Open(Bracket::Round) => {
                global.tokens.next();

                let (args, named_args) = function_arguments(global, imperative, buffer)?;
                assert!(
                    named_args.is_empty(),
                    "Named arguments temporarily unsupported"
                );

                value = buffer.add(Node::new(
                    loc,
                    NodeKind::FunctionCall {
                        calling: value,
                        args,
                    },
                ));
            }
            _ => break,
        }
    }

    Ok(value)
}

fn function_type(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    loc: Location,
    buffer: &mut AstBuilder,
) -> Result<NodeId, ()> {
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
        args.push(arg_type);

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
        buffer.add(Node::new(
            loc,
            NodeKind::LiteralType(TypeKind::Empty.into()),
        ))
    };

    Ok(buffer.add(Node::new(loc, NodeKind::FunctionType { args, returns })))
}

fn function_arguments(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut AstBuilder,
) -> Result<(NodeList, NamedNodeList), ()> {
    let mut args = Vec::new();
    loop {
        if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
            break;
        }

        let arg = expression(global, imperative, buffer)?;

        args.push(arg);

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

    Ok((args, vec![]))
}

/// Parses a function declaration, although doesn't expect the 'fn' keyword to be included because
/// that keyword was what triggered this function to be called in the first place.
fn function_declaration(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut AstBuilder,
    loc: Location,
) -> Result<NodeId, ()> {
    global
        .tokens
        .expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;

    imperative.push_scope_boundary();

    let mut args = Vec::new();
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
            if global.tokens.try_consume_operator_string(":").is_some() {
                let arg_type = type_(global, imperative, buffer)?;
                let local_id = imperative.insert_local(Local::new(loc, name));
                args.push((local_id, arg_type));
            } else {
                global.error(
                    global.tokens.loc(),
                    "Expected ':' for argument type".to_string(),
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

    let returns = if global.tokens.try_consume_operator_string("->").is_some() {
        type_(global, imperative, buffer)?
    } else {
        buffer.add(Node::new(
            global.tokens.loc(),
            NodeKind::LiteralType(TypeKind::Empty.into()),
        ))
    };

    let body = expression(global, imperative, buffer)?;

    imperative.pop_scope_boundary();

    Ok(buffer.add(Node::new(
        loc,
        NodeKind::FunctionDeclaration {
            args,
            returns: returns,
            body,
        },
    )))
}

fn maybe_parse_polymorphic_arguments(
    global: &mut DataContext<'_>,
) -> Result<Vec<(Location, Ustr)>, ()> {
    let mut args = Vec::new();

    if global.tokens.try_consume_operator_string(".").is_some() {
        global.tokens.expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;

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
                TokenKind::Close(Bracket::Round) => break,
                TokenKind::Comma => {}
                _ => {
                    global.error(token.loc, "Expected either ',' or ')'".to_string());
                    return Err(());
                }
            }
        }
    }
    Ok(args)
}

fn parse_pointer_permits(global: &mut DataContext<'_>) -> Option<(Location, PtrPermits)> {
    match global.tokens.peek() {
        Some(&Token {
            kind: TokenKind::Keyword(Keyword::Write),
            loc,
            ..
        }) => {
            global.tokens.next();
            Some((loc, PtrPermits::WRITE))
        }
        Some(&Token {
            kind: TokenKind::Keyword(Keyword::Read),
            loc,
            ..
        }) => {
            global.tokens.next();
            Some((loc, PtrPermits::READ))
        }
        Some(&Token {
            kind: TokenKind::Keyword(Keyword::ReadWrite),
            loc,
            ..
        }) => {
            global.tokens.next();
            Some((loc, PtrPermits::READ_WRITE))
        }
        // Leave to be inferred.
        _ => {
            if let Some(loc) = global.tokens.try_consume_operator_string("!!") {
                Some((loc, PtrPermits::NONE))
            } else {
                None
            }
        }
    }
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
            type_infer_value_id: 0,
            stack_frame_id: 0,
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
                type_infer_value_id: 0,
                stack_frame_id: 0,
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
