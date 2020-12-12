pub mod ast;
mod context;
mod lexer;
mod token_stream;

use crate::dependencies::{DependencyKind, DependencyList};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::locals::Local;
use crate::location::Location;
use crate::operators::{AccessOp, BinaryOp};
use crate::program::{Program, Task};
use crate::self_buffer::{SelfBuffer, SelfTree};
use crate::types::TypeKind;
pub use ast::{Node, NodeKind};
use context::{DataContext, ImperativeContext};
use lexer::{Bracket, Keyword, Token, TokenKind};
use std::path::Path;
use ustr::Ustr;

pub type Ast = SelfTree<Node>;

pub fn process_string(
    errors: &mut ErrorCtx,
    program: &Program,
    file: &Path,
    string: &str,
) -> Result<(), ()> {
    let file_name_str = file.to_str().expect("File path is not a valid string, this should not happen since all paths are constructed from strings originally").into();

    // If the file has already been parsed, do not parse it again!
    if !program.loaded_files.lock().insert(file_name_str) {
        program.logger.log(format_args!(
            "File {} was already loaded, so didn't parse it again",
            file_name_str
        ));
        return Ok(());
    }

    let mut tokens = lexer::process_string(errors, file_name_str, string)?;

    let mut context = DataContext::new(errors, program, &mut tokens, &file);

    while let Some(token) = context.tokens.next() {
        match token.kind {
            TokenKind::Keyword(Keyword::Const) => constant(&mut context)?,
            TokenKind::Keyword(Keyword::Library) => {
                let name = context.tokens.expect_next(context.errors)?;
                if let TokenKind::Literal(Literal::String(name)) = name.kind {
                    context
                        .tokens
                        .expect_next_is(context.errors, &TokenKind::SemiColon)?;

                    let mut path = context.program.arguments.lib_path.to_path_buf();
                    path.push(&name);
                    program.add_file(path);
                } else {
                    context.error(
                        name.loc,
                        "Expected string literal for file name".to_string(),
                    );
                    return Err(());
                }
            }
            TokenKind::Keyword(Keyword::Import) => {
                let name = context.tokens.expect_next(context.errors)?;
                if let TokenKind::Literal(Literal::String(name)) = name.kind {
                    context
                        .tokens
                        .expect_next_is(context.errors, &TokenKind::SemiColon)?;

                    let mut path = context.path.to_path_buf();
                    path.pop();
                    path.push(&name);
                    program.add_file(path);
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
        let polymorphic_parameters = maybe_parse_polymorphic_arguments(global)?;

        if global.tokens.try_consume_operator_string("=").is_none() {
            global.error(token.loc, "Expected '=' after const".to_string());
            return Err(());
        }

        let mut buffer = SelfBuffer::new();

        let mut dependencies = DependencyList::new();
        let mut imperative = ImperativeContext::new(&mut dependencies, false);
        let expr = expression(global, &mut imperative, &mut buffer)?;
        let tree = buffer.insert_root(expr);

        let locals = imperative.locals;

        if polymorphic_parameters.is_empty() {
            let id = global
                .program
                .define_member(global.errors, token.loc, name)?;
            global
                .program
                .queue_task(id, dependencies, Task::Type(id, locals, tree));
        } else {
            // global.program.insert_polymorphic(
            //     global.errors,
            //     token.loc,
            //     name,
            //     dependencies,
            //     true,
            // )?;
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

        let right = value(global, imperative, buffer)?;
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
        let type_bound = type_(global, &mut imperative.dependencies, buffer)?;
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

/// A value allows for unary operators and member accesses or function insertions.
/// However, unary operators are only allowed before the accesses.
fn value(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut SelfBuffer,
) -> Result<Node, ()> {
    if let Some((loc, op)) = global.tokens.try_consume_operator() {
        let operand = value(global, imperative, buffer)?;
        Ok(Node::new(
            loc,
            NodeKind::Unary {
                operand: buffer.insert(operand),
                op,
            },
        ))
    } else {
        member_value(global, imperative, buffer)
    }
}

/// A member value only allows for member accesses or function insertions. It does not
/// allow for unary operators.
fn member_value(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut SelfBuffer,
) -> Result<Node, ()> {
    let mut value = atom_value(global, imperative, buffer)?;

    while let Some((_, op)) = global.tokens.try_consume_operator() {
        match op {
            AccessOp::Member => {
                let token = global.tokens.expect_next(global.errors)?;
                if let TokenKind::Identifier(name) = token.kind {
                    value = Node::new(
                        token.loc,
                        NodeKind::Member {
                            of: buffer.insert(value),
                            name,
                        },
                    );
                } else {
                    global.error(token.loc, "Expected identifier".to_string());
                }
            }
        }
    }

    Ok(value)
}

fn type_(
    global: &mut DataContext<'_>,
    dependencies: &mut DependencyList,
    buffer: &mut SelfBuffer,
) -> Result<Node, ()> {
    let token = global.tokens.expect_peek(global.errors)?;
    let loc = token.loc;
    match token.kind {
        TokenKind::Identifier(name) => {
            global.tokens.next();
            dependencies.add(loc, name, DependencyKind::Value);
            Ok(Node::new(loc, NodeKind::GlobalForTyping(name)))
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

                let field_type = type_(global, dependencies, buffer)?;
                fields.push((name, buffer.insert(field_type)));

                let token = global.tokens.expect_next(global.errors)?;
                match token.kind {
                    TokenKind::Close(Bracket::Curly) => break,
                    TokenKind::Comma => {}
                    _ => {
                        global.error(token.loc, "Expected ',' or ')'".to_string());
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
                    let inner = type_(global, dependencies, buffer)?;
                    Ok(Node::new(loc, NodeKind::BufferType(buffer.insert(inner))))
                }
                _ => {
                    let mut imperative = ImperativeContext::new(dependencies, true);
                    let len = expression(global, &mut imperative, buffer)?;
                    global
                        .tokens
                        .expect_next_is(global.errors, &TokenKind::Close(Bracket::Square))?;
                    let locals = imperative.locals;

                    let inner = type_(global, dependencies, buffer)?;

                    Ok(Node::new(
                        loc,
                        NodeKind::ArrayType {
                            len: (locals, buffer.insert(len)),
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
                let inner = type_(global, dependencies, buffer)?;
                global
                    .tokens
                    .expect_next_is(global.errors, &TokenKind::Close(Bracket::Round))?;
                Ok(inner)
            }
        }
        TokenKind::Keyword(Keyword::Extern) => {
            global.tokens.next();
            global
                .tokens
                .expect_next_is(global.errors, &TokenKind::Keyword(Keyword::Function))?;
            function_type(global, dependencies, loc, buffer, true)
        }
        TokenKind::Keyword(Keyword::Function) => {
            global.tokens.next();
            function_type(global, dependencies, loc, buffer, false)
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
                let inner = type_(global, dependencies, buffer)?;
                Ok(Node::new(
                    loc,
                    NodeKind::ReferenceType(buffer.insert(inner)),
                ))
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

/// A value without unary operators, member accesses, or anything like that.
fn atom_value(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    buffer: &mut SelfBuffer,
) -> Result<Node, ()> {
    let mut value = {
        let token = global.tokens.expect_next(global.errors)?;
        match token.kind {
            TokenKind::Identifier(name) => {
                if let Some(local_id) = imperative.get_local(name) {
                    Node::new(token.loc, NodeKind::Local(local_id))
                } else if imperative.evaluate_at_typing {
                    imperative
                        .dependencies
                        .add(token.loc, name, DependencyKind::Value);
                    Node::new(token.loc, NodeKind::GlobalForTyping(name))
                } else {
                    imperative
                        .dependencies
                        .add(token.loc, name, DependencyKind::Type);
                    Node::new(token.loc, NodeKind::Global(name))
                }
            }
            TokenKind::Literal(literal) => Node::new(token.loc, NodeKind::Literal(literal)),
            TokenKind::Keyword(Keyword::Type) => {
                let t = type_(global, &mut imperative.dependencies, buffer)?;
                Node::new(token.loc, NodeKind::TypeAsValue(buffer.insert(t)))
            }
            TokenKind::Keyword(Keyword::Break) => {
                let (loc, label_name) = global.tokens.expect_identifier(global.errors)?;

                let id = match imperative.get_label(label_name) {
                    Some(id) => id,
                    None => {
                        global.error(loc, format!("There is no label called '{}'", label_name));
                        return Err(());
                    }
                };

                let num_defer_deduplications = imperative.locals.get_label(id).num_defers;
                let value = expression(global, imperative, buffer)?;
                Node::new(
                    token.loc,
                    NodeKind::Break {
                        label: id,
                        num_defer_deduplications,
                        value: buffer.insert(value),
                    },
                )
            }
            TokenKind::Keyword(Keyword::While) => {
                let condition = expression(global, imperative, buffer)?;
                let body = value(global, imperative, buffer)?;
                Node::new(
                    token.loc,
                    NodeKind::While {
                        condition: buffer.insert(condition),
                        body: buffer.insert(body),
                    },
                )
            }
            TokenKind::Keyword(Keyword::If) => {
                let condition = expression(global, imperative, buffer)?;
                let true_body = value(global, imperative, buffer)?;

                let false_body = if global
                    .tokens
                    .try_consume(&TokenKind::Keyword(Keyword::Else))
                {
                    Some(value(global, imperative, buffer)?)
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
            TokenKind::Keyword(Keyword::Function) => {
                function_declaration(global, imperative.dependencies, buffer, token.loc)?
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
            TokenKind::Keyword(Keyword::Extern) => {
                let loc = token.loc;
                let token = global.tokens.expect_next(global.errors)?;
                if let TokenKind::Literal(Literal::String(library_name)) = token.kind {
                    let token = global.tokens.expect_next(global.errors)?;
                    if let TokenKind::Literal(Literal::String(symbol_name)) = token.kind {
                        let mut library_path = global.path.to_path_buf();
                        library_path.pop();
                        library_path.push(&library_name);
                        Node::new(
                            loc,
                            NodeKind::Extern {
                                library_name: library_path,
                                symbol_name,
                            },
                        )
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

                expr
            }

            TokenKind::Open(Bracket::Curly) => {
                let label = maybe_parse_label(global, imperative)?;

                imperative.push_scope_boundary();

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
                                let id = imperative.insert_local(Local {
                                    loc: token.loc,
                                    name,
                                    type_: None,
                                    value: None,
                                });

                                global.tokens.try_consume_operator_string("=").ok_or_else(
                                    || {
                                        global.error(
                                            token.loc,
                                            "Expected '=' after identifier".into(),
                                        );
                                    },
                                )?;

                                let value = expression(global, imperative, buffer)?;

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
        }
    };

    // FIXME: This should be done in frigging members
    while let Some(loc) = global
        .tokens
        .try_consume_with_data(&TokenKind::Open(Bracket::Round))
    {
        let mut args = Vec::new();
        loop {
            if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
                break;
            }

            let arg = expression(global, imperative, buffer)?;
            args.push(buffer.insert(arg));

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

        if args.len() >= crate::MAX_FUNCTION_ARGUMENTS {
            global.error(
                loc,
                format!(
                    "There can at most be {} arguments in a function",
                    crate::MAX_FUNCTION_ARGUMENTS
                ),
            );
            return Err(());
        }

        value = Node::new(
            loc,
            NodeKind::FunctionCall {
                calling: buffer.insert(value),
                args,
            },
        );
    }

    Ok(value)
}

fn function_type(
    global: &mut DataContext<'_>,
    dependencies: &mut DependencyList,
    loc: Location,
    buffer: &mut SelfBuffer,
    is_extern: bool,
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

        let arg_type = type_(global, dependencies, buffer)?;
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
        type_(global, dependencies, buffer)?
    } else {
        Node::new(loc, NodeKind::LiteralType(TypeKind::Empty.into()))
    };

    Ok(Node::new(
        loc,
        NodeKind::FunctionType {
            is_extern,
            args,
            returns: buffer.insert(returns),
        },
    ))
}

/// Parses a function declaration, although doesn't expect the 'fn' keyword to be included because
/// that keyword was what triggered this function to be called in the first place.
fn function_declaration(
    global: &mut DataContext<'_>,
    dependencies: &mut DependencyList,
    buffer: &mut SelfBuffer,
    loc: Location,
) -> Result<Node, ()> {
    global
        .tokens
        .expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;

    let mut imperative = ImperativeContext::new(dependencies, false);
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
            imperative.insert_local(Local {
                loc,
                name,
                type_: None,
                value: None,
            });

            if global.tokens.try_consume_operator_string(":").is_none() {
                global.error(
                    global.tokens.loc(),
                    "Expected ':' for argument type".to_string(),
                );
                return Err(());
            }

            let arg_type = type_(global, imperative.dependencies, buffer)?;
            args.push(buffer.insert(arg_type));
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
        type_(global, imperative.dependencies, buffer)?
    } else {
        Node::new(
            global.tokens.loc(),
            NodeKind::LiteralType(TypeKind::Empty.into()),
        )
    };

    let body = expression(global, &mut imperative, buffer)?;

    Ok(Node::new(
        loc,
        NodeKind::FunctionDeclaration {
            locals: imperative.locals,
            args,
            returns: buffer.insert(returns),
            body: buffer.insert(body),
        },
    ))
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

fn maybe_parse_label(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
) -> Result<Option<crate::locals::LabelId>, ()> {
    if global.tokens.try_consume(&TokenKind::SingleQuote) {
        let (loc, name) = global.tokens.expect_identifier(global.errors)?;
        let id = imperative.insert_label(crate::locals::Label {
            name,
            loc,
            defer_depth: imperative.defer_depth,
            num_defers: 0,
            type_: None,
            value: None,
            ir_labels: None,
        });
        Ok(Some(id))
    } else {
        Ok(None)
    }
}
