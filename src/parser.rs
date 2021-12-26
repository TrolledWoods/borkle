use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::locals::{Local, LocalVariables};
use crate::location::Location;
use crate::operators::{BinaryOp, Operator, UnaryOp};
use crate::program::{Program, ScopeId, Task};
use crate::types::{Type, TypeKind};
pub use ast::{AstBuilder, AstSlot, Node, NodeId, NodeKind, FinishedNode, Muncher};
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

    while let Some(token) = context.tokens.peek() {
        // @Hack: Workaround for the borrowing errors
        let token = token.clone();

        match token.kind {
            TokenKind::Keyword(Keyword::Const) => {
                context.tokens.next();
                constant(&mut context)?
            }
            TokenKind::Keyword(Keyword::Library) => {
                context.tokens.next();
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
                context.tokens.next();

                let mut buffer = AstBuilder::new();
                let mut dependencies = DependencyList::new();
                let mut locals = LocalVariables::new();
                let mut imperative =
                    ImperativeContext::new(&mut dependencies, &mut locals, false, &[]);
                expression(&mut context, &mut imperative, buffer.add())?;
                let tree = buffer.finish();

                context
                    .tokens
                    .expect_next_is(context.errors, &TokenKind::SemiColon)?;

                let id = context.program.define_member(
                    context.errors,
                    token.loc,
                    None,
                    "<entry_point>".into(),
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
                context.tokens.next();

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
                let mut buffer = AstBuilder::new();

                let mut dependencies = DependencyList::new();
                let mut locals = LocalVariables::new();
                let mut imperative = ImperativeContext::new(
                    &mut dependencies,
                    &mut locals,
                    false,
                    &[],
                );
                expression(&mut context, &mut imperative, buffer.add())?;
                let tree = buffer.finish();

                let id = context
                    .program
                    .define_member(context.errors, token.loc, None, "<anonymous>".into())?;

                context.program.queue_task(
                    dependencies,
                    Task::TypeMember { member_id: id, locals, ast: tree },
                );

                context
                    .tokens
                    .expect_next_is(context.errors, &TokenKind::SemiColon)?;
            }
        }
    }

    Ok(())
}

fn constant(global: &mut DataContext<'_>) -> Result<(), ()> {
    let token = global.tokens.expect_next(global.errors)?;
    if let TokenKind::Identifier(name) = token.kind {
        let poly_args = maybe_parse_polymorphic_arguments(global)?;

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
            &poly_args,
        );
        expression(global, &mut imperative, buffer.add())?;
        let tree = buffer.finish();

        if poly_args.is_empty() {
            let id = global
                .program
                .define_member(global.errors, token.loc, Some(global.scope), name)?;
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
                poly_args.len(),
            )?;
            global.program.queue_task(
                dependencies.clone(),
                Task::TypePolyMember {
                    member_id: id,
                    locals,
                    ast: tree,
                    dependencies,
                    poly_args,
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
    slot: AstSlot<'_>,
) -> Result<FinishedNode, ()> {
    let expr = expression_rec(global, imperative, slot, 0)?;

    Ok(expr)
}

fn expression_rec(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    slot: AstSlot<'_>,
    precedence: usize,
) -> Result<FinishedNode, ()> {
    let mut muncher = slot.into_muncher();

    value(global, imperative, muncher.add())?;

    while let Some((loc, op)) = global
        .tokens
        .try_consume_operator_with_precedence(precedence)
    {
        // @Improvement: Reimplement `has_to_be_alone`

        if op == BinaryOp::TypeBound {
            type_(global, imperative, muncher.add())?;
            muncher.munch(2, loc, NodeKind::TypeBound);
        } else {
            expression_rec(global, imperative, muncher.add(), op.precedence())?;
            muncher.munch(2, loc, NodeKind::Binary { op });
        }
    }

    Ok(muncher.finish())
}

fn type_(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    mut slot: AstSlot<'_>,
) -> Result<FinishedNode, ()> {
    let token = global.tokens.expect_peek(global.errors)?;
    let loc = token.loc;
    match token.kind {
        TokenKind::Keyword(Keyword::TypeOf) => {
            global.tokens.next();

            // @TODO: We want to tell the parser about
            // the fact that we don't actually need the values of anything
            // in here, so that it doesn't fetch them unnecessarily
            value(global, imperative, slot.add())?;

            Ok(slot.finish(loc, NodeKind::TypeOf))
        }
        TokenKind::Identifier(name) => {
            global.tokens.next();

            if let Some(index) = imperative
                .poly_args
                .iter()
                .position(|(_, arg)| *arg == name)
            {
                Ok(slot.finish(loc, NodeKind::PolymorphicArgument(index)))
            } else {
                imperative.dependencies.add(
                    loc,
                    DepKind::MemberByName(
                        global.scope,
                        name,
                        MemberDep::ValueAndCallableIfFunction,
                    ),
                );

                Ok(slot.finish(loc, NodeKind::Global { scope: global.scope, name }))
            }
        }
        TokenKind::Keyword(Keyword::Underscore) => {
            global.tokens.next();

            Ok(slot.finish(loc, NodeKind::ImplicitType))
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

                type_(global, imperative, slot.add())?;
                fields.push(name);

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

            Ok(slot.finish(loc, NodeKind::StructType { fields }))
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
                        Ok(slot.finish(
                            loc,
                            NodeKind::LiteralType(TypeKind::VoidBuffer.into()),
                        ))
                    } else {
                        type_(global, imperative, slot.add())?;
                        Ok(slot.finish(loc, NodeKind::BufferType))
                    }
                }
                _ => {
                    let old_evaluate_at_typing = imperative.evaluate_at_typing;
                    imperative.evaluate_at_typing = true;
                    expression(global, imperative, slot.add())?;
                    global
                        .tokens
                        .expect_next_is(global.errors, &TokenKind::Close(Bracket::Square))?;
                    imperative.evaluate_at_typing = old_evaluate_at_typing;
                    type_(global, imperative, slot.add())?;

                    Ok(slot.finish(
                        loc,
                        NodeKind::ArrayType,
                    ))
                }
            }
        }
        TokenKind::Open(Bracket::Round) => {
            global.tokens.next();
            if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
                Ok(slot.finish(
                    loc,
                    NodeKind::LiteralType(TypeKind::Empty.into()),
                ))
            } else {
                type_(global, imperative, slot.add())?;
                global
                    .tokens
                    .expect_next_is(global.errors, &TokenKind::Close(Bracket::Round))?;
                Ok(slot.finish(loc, NodeKind::Parenthesis))
            }
        }
        TokenKind::Keyword(Keyword::Function) => {
            global.tokens.next();
            function_type(global, imperative, loc, slot)
        }
        TokenKind::Keyword(Keyword::Bool) => {
            global.tokens.next();
            Ok(slot.finish(loc, NodeKind::LiteralType(TypeKind::Bool.into())))
        }
        TokenKind::Type(type_) => {
            global.tokens.next();
            Ok(slot.finish(loc, NodeKind::LiteralType(type_)))
        }
        TokenKind::PrimitiveInt(type_) => {
            global.tokens.next();
            Ok(slot.finish(loc, NodeKind::LiteralType(type_.into())))
        }
        _ => {
            if global.tokens.try_consume_operator_string("&").is_some() {
                if global
                    .tokens
                    .try_consume(&TokenKind::Keyword(Keyword::Void))
                {
                    // @TODO: This type should also have pointer permits
                    Ok(slot.finish(
                        loc,
                        NodeKind::LiteralType(Type::new(TypeKind::VoidPtr)),
                    ))
                } else if global.tokens.try_consume(&TokenKind::Keyword(Keyword::Any)) {
                    // @TODO: This type should also have pointer permits
                    Ok(slot.finish(
                        loc,
                        NodeKind::LiteralType(Type::new(TypeKind::AnyPtr)),
                    ))
                } else {
                    type_(global, imperative, slot.add())?;
                    Ok(slot.finish(loc, NodeKind::ReferenceType))
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
    mut slot: AstSlot<'_>,
) -> Result<FinishedNode, ()> {
    if let Some((loc, op)) = global.tokens.try_consume_operator() {
        if op == UnaryOp::Reference {
            value(global, imperative, slot.add())?;
            Ok(slot.finish(loc, NodeKind::Reference))
        } else {
            value(global, imperative, slot.add())?;
            Ok(slot.finish(loc, NodeKind::Unary { op }))
        }
    } else {
        value_without_unaries(global, imperative, slot)
    }
}

/// A value
fn value_without_unaries(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    base_slot: AstSlot<'_>,
) -> Result<FinishedNode, ()> {
    let mut muncher = base_slot.into_muncher();
    let token = global.tokens.expect_next(global.errors)?;
    let loc = token.loc;

    let mut slot = muncher.add();
    match token.kind {
        TokenKind::Keyword(Keyword::Underscore) => {
            slot.finish(token.loc, NodeKind::ImplicitType)
        }
        TokenKind::Identifier(name) => {
            if let Some(local_id) = imperative.get_local(name) {
                let local = imperative.locals.get_mut(local_id);
                local.num_uses += 1;
                local.uses.push(token.loc);
                slot.finish(token.loc, NodeKind::Local(local_id))
            } else if let Some(index) = imperative
                .poly_args
                .iter()
                .position(|(_, arg)| *arg == name)
            {
                slot.finish(token.loc, NodeKind::PolymorphicArgument(index))
            } else {
                imperative.dependencies.add(
                    token.loc,
                    DepKind::MemberByName(
                        global.scope,
                        name,
                        if imperative.evaluate_at_typing { MemberDep::ValueAndCallableIfFunction } else { MemberDep::Type },
                    ),
                );
                slot.finish(
                    token.loc,
                    NodeKind::Global { scope: global.scope, name },
                )
            }
        }
        TokenKind::Literal(literal) => slot.finish(token.loc, NodeKind::Literal(literal)),
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

            slot.finish(
                token.loc,
                NodeKind::BuiltinFunction(builtin_kind),
            )
        }
        TokenKind::Keyword(Keyword::Const) => {
            // @TODO: Prevent cross-referencing of variable values here!!!!!!!!!!!
            // Could probably do it just by looking at what scope_id local reads/writes have,
            // as well as what scope_id the declarations of locals have. That should be all that's necessary....
            let old_in_const_expr = imperative.in_const_expression;
            imperative.in_const_expression = true;
            expression(global, imperative, slot.add())?;
            imperative.in_const_expression = old_in_const_expr;

            if imperative.evaluate_at_typing {
                slot.finish(token.loc, NodeKind::ConstAtTyping)
            } else {
                slot.finish(token.loc, NodeKind::ConstAtEvaluation)
            }
        }
        TokenKind::Keyword(Keyword::SizeOf) => {
            type_(global, imperative, slot.add())?;
            slot.finish(token.loc, NodeKind::SizeOf)
        }
        TokenKind::Keyword(Keyword::Explain) => {
            expression(global, imperative, slot.add())?;

            slot.finish(
                token.loc,
                NodeKind::Explain,
            )
        }
        TokenKind::Keyword(Keyword::Type) => {
            type_(global, imperative, slot.add())?;
            slot.finish(token.loc, NodeKind::TypeAsValue)
        }
        TokenKind::PrimitiveInt(type_) => {
            slot.add().finish(token.loc, NodeKind::LiteralType(type_.into()));
            slot.finish(token.loc, NodeKind::TypeAsValue)
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

            if let Some(&Token {
                loc,
                kind: TokenKind::SemiColon,
            }) = global.tokens.peek()
            {
                slot.add().finish(loc, NodeKind::Empty);
            } else {
                expression(global, imperative, slot.add())?;
            }

            let label_mut = imperative.locals.get_label_mut(id);
            if label_mut.first_break_location.is_none() {
                label_mut.first_break_location = Some(loc);
            }

            slot.finish(
                token.loc,
                NodeKind::Break {
                    label: id,
                    num_defer_deduplications,
                },
            )
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

            expression(global, imperative, slot.add())?;

            let iterator = imperative.insert_local(iterator_local);
            let iteration_var = imperative.insert_local(Local::new(token.loc, "_iters".into()));

            expression(global, imperative, slot.add())?;

            imperative.pop_default_label();
            imperative.pop_scope_boundary();

            if global
                .tokens
                .try_consume(&TokenKind::Keyword(Keyword::Else))
            {
                expression(global, imperative, slot.add())?;
            } else {
                slot.add().finish(loc, NodeKind::Empty);
            }

            slot.finish(
                token.loc,
                NodeKind::For {
                    iterator,
                    iteration_var,
                    label,
                },
            )
        }
        TokenKind::Keyword(Keyword::While) => {
            imperative.push_scope_boundary();
            let label = parse_default_label(global, imperative)?;

            let iteration_var = imperative.insert_local(Local::new(token.loc, "_iters".into()));

            expression(global, imperative, slot.add())?;
            expression(global, imperative, slot.add())?;

            imperative.pop_default_label();
            imperative.pop_scope_boundary();

            if global
                .tokens
                .try_consume(&TokenKind::Keyword(Keyword::Else))
            {
                expression(global, imperative, slot.add())?;
            } else {
                slot.add().finish(loc, NodeKind::Empty);
            }

            slot.finish(
                token.loc,
                NodeKind::While {
                    iteration_var,
                    label,
                },
            )
        }
        TokenKind::Keyword(Keyword::If) => {
            // Parse tags
            let mut is_const = None;

            parse_tags(global, imperative, "if", &mut [
                ("const".into(), &mut is_const),
            ])?;

            expression(global, imperative, slot.add())?;
            expression(global, imperative, slot.add())?;

            if global
                .tokens
                .try_consume(&TokenKind::Keyword(Keyword::Else))
            {
                expression(global, imperative, slot.add())?;
            } else {
                slot.add().finish(loc, NodeKind::Empty);
            }

            slot.finish(
                token.loc,
                NodeKind::If {
                    is_const,
                },
            )
        }
        TokenKind::Keyword(Keyword::Uninit) => slot.finish(token.loc, NodeKind::Uninit),
        TokenKind::Keyword(Keyword::Zeroed) => slot.finish(token.loc, NodeKind::Zeroed),
        TokenKind::Keyword(Keyword::Function) => {
            function_declaration(global, imperative, slot, token.loc)?
        }
        TokenKind::Keyword(Keyword::Cast) => {
            value(global, imperative, slot.add())?;
            slot.finish(token.loc, NodeKind::Cast)
        }
        TokenKind::Keyword(Keyword::BitCast) => {
            value(global, imperative, slot.add())?;
            slot.finish(token.loc, NodeKind::BitCast)
        }
        TokenKind::Open(Bracket::Square) => {
            loop {
                if global
                    .tokens
                    .try_consume(&TokenKind::Close(Bracket::Square))
                {
                    break;
                }

                expression(global, imperative, slot.add())?;

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

            slot.finish(token.loc, NodeKind::ArrayLiteral)
        }
        TokenKind::Open(Bracket::Round) => {
            expression(global, imperative, slot.add())?;

            global
                .tokens
                .expect_next_is(global.errors, &TokenKind::Close(Bracket::Round))?;

            slot.finish(token.loc, NodeKind::Parenthesis)
        }

        TokenKind::Open(Bracket::Curly) => {
            imperative.push_scope_boundary();

            let label = maybe_parse_label(global, imperative)?;

            loop {
                if let Some(loc) = global
                    .tokens
                    .try_consume_with_data(&TokenKind::Close(Bracket::Curly))
                {
                    slot.add().finish(loc, NodeKind::Empty);
                    break;
                }

                let peek_token = global.tokens.expect_peek(global.errors)?;
                let loc = peek_token.loc;
                match peek_token.kind {
                    TokenKind::Keyword(Keyword::Defer) => {
                        global.tokens.next();

                        let mut defer_node = slot.add();
                        expression(global, imperative, defer_node.add())?;
                        defer_node.finish(loc, NodeKind::Defer);

                        imperative.defer_depth += 1;

                        if let Some(label) = label {
                            imperative.locals.get_label_mut(label).num_defers += 1;
                        }
                    }
                    TokenKind::Keyword(Keyword::Let) => {
                        global.tokens.next();
                        let token = global.tokens.expect_next(global.errors)?;
                        if let TokenKind::Identifier(name) = token.kind {
                            let equals = global
                                .tokens
                                .try_consume_operator_string("=")
                                .ok_or_else(|| {
                                    global.error(token.loc, "Expected '=' after identifier".into());
                                })?;

                            let mut let_node = slot.add();
                            expression(global, imperative, let_node.add())?;

                            let id = imperative.insert_local(Local::new(token.loc, name));

                            let_node.finish(
                                equals,
                                NodeKind::Declare {
                                    local: id,
                                },
                            );
                        } else {
                            global.error(token.loc, "Expected identifier".to_string());
                            return Err(());
                        }
                    }
                    _ => {
                        expression(global, imperative, slot.add())?;
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
            slot.finish(token.loc, NodeKind::Block { label })
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
                        muncher.munch(1, loc, NodeKind::Member { name });
                    }
                    TokenKind::Open(Bracket::Round) => {
                        let old_evaluate_at_typing = imperative.evaluate_at_typing;
                        imperative.evaluate_at_typing = true;
                        let count = function_arguments(global, imperative, &mut muncher)?;
                        imperative.evaluate_at_typing = old_evaluate_at_typing;

                        muncher.munch(count + 1, loc, NodeKind::PolymorphicArgs);
                    }
                    _ => {
                        global.error(token.loc, "Expected either an identifier, or a generic argument list".to_string());
                        return Err(());
                    }
                }
            }
            TokenKind::Open(Bracket::Round) => {
                global.tokens.next();

                let count = function_arguments(global, imperative, &mut muncher)?;
                muncher.munch(count + 1, loc, NodeKind::FunctionCall);
            }
            _ => break,
        }
    }

    Ok(muncher.finish())
}

fn function_type(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    loc: Location,
    mut slot: AstSlot<'_>,
) -> Result<FinishedNode, ()> {
    // We start with a list of arguments.
    global
        .tokens
        .expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;

    loop {
        if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
            break;
        }

        type_(global, imperative, slot.add())?;

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

    if global.tokens.try_consume_operator_string("->").is_some() {
        type_(global, imperative, slot.add())?;
    } else {
        slot.add().finish(
            loc,
            NodeKind::LiteralType(TypeKind::Empty.into()),
        );
    };

    Ok(slot.finish(loc, NodeKind::FunctionType))
}

fn function_arguments(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    muncher: &mut Muncher<'_>,
) -> Result<u32, ()> {
    let mut count = 0;
    loop {
        if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
            break;
        }

        expression(global, imperative, muncher.add())?;
        count += 1;

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

    Ok(count)
}

/// Parses a function declaration, although doesn't expect the 'fn' keyword to be included because
/// that keyword was what triggered this function to be called in the first place.
fn function_declaration(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    mut slot: AstSlot<'_>,
    loc: Location,
) -> Result<FinishedNode, ()> {
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
            let local_id = imperative.insert_local(Local::new(loc, name));
            args.push(local_id);

            if global.tokens.try_consume_operator_string(":").is_some() {
                type_(global, imperative, slot.add())?;
            } else {
                slot.add().finish(loc, NodeKind::ImplicitType);
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

    if global.tokens.try_consume_operator_string("->").is_some() {
        type_(global, imperative, slot.add())?;
    } else {
        slot.add().finish(loc, NodeKind::ImplicitType);
    }

    expression(global, imperative, slot.add())?;

    imperative.pop_scope_boundary();

    Ok(slot.finish(
        loc,
        NodeKind::FunctionDeclaration {
            args,
        },
    ))
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

fn parse_tags(global: &mut DataContext<'_>, _imperative: &mut ImperativeContext<'_>, expr_name: &str, tags: &mut [(Ustr, &mut Option<Location>)]) -> Result<(), ()> {
    let mut is_first = true;
    loop {
        let Some(&Token { loc, kind: TokenKind::Tag(tag_name), .. }) = global.tokens.peek() else {
            if is_first {
                break;
            } else {
                global.error(global.tokens.loc(), format!("Expected tag for `{}`. You need a `:` after a tag list to close it", expr_name));
                return Err(());
            }
        };

        is_first = false;

        global.tokens.next();

        if let Some((_, tag)) = tags.iter_mut().find(|(name, _)| *name == tag_name) {
            if let Some(old) = tag {
                global.errors.info(*old, "Defined previously here".to_string());
                global.error(loc, format!("tag `{}` defined twice", tag_name));
            } else {
                **tag = Some(loc);
            }
        } else {
            global.error(loc, format!("no tag `{}` on `{}`", tag_name, expr_name));
        }

        if global.tokens.try_consume_operator_string(":").is_some() {
            break;
        } else {
            global.tokens.expect_next_is(global.errors, &TokenKind::Comma)?;
        }
    }

    Ok(())
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
