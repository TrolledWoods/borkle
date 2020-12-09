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
use crate::types::TypeKind;
pub use ast::{Node, NodeKind};
use bump_tree::Tree;
use context::{DataContext, ImperativeContext};
use lexer::{Bracket, Keyword, Token, TokenKind};
use std::convert::TryFrom;
use std::path::PathBuf;

pub type Ast = Tree<Node>;
type NodeBuilder<'a> = bump_tree::NodeBuilder<'a, Node>;

pub fn process_string(
    errors: &mut ErrorCtx,
    program: &Program,
    file: PathBuf,
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
        if global.tokens.try_consume_operator_string("=").is_none() {
            global.error(token.loc, "Expected '=' after const".to_string());
            return Err(());
        }

        let mut ast = Ast::new();

        let mut dependencies = DependencyList::new();
        let mut imperative = ImperativeContext::new(&mut dependencies);
        expression(global, &mut imperative, ast.builder())?;
        let locals = imperative.locals;
        ast.set_root();

        global
            .program
            .insert(global.errors, token.loc, name, dependencies, true, |id| {
                Task::Type(id, locals, ast)
            })?;

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
    imperative: &mut ImperativeContext<'_>,
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
    imperative: &mut ImperativeContext<'_>,
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
    let token = global.tokens.expect_peek(global.errors)?;
    let loc = token.loc;
    match token.kind {
        TokenKind::Identifier(name) => {
            global.tokens.next();
            dependencies.add(loc, name, DependencyKind::Value);
            node.set(Node::new(loc, NodeKind::Global(name)));
            node.validate();
        }
        TokenKind::Open(Bracket::Square) => {
            global.tokens.next();
            let token = global.tokens.expect_next(global.errors)?;
            match token.kind {
                TokenKind::Close(Bracket::Square) => {
                    type_(global, dependencies, node.arg())?;
                    node.set(Node::new(loc, NodeKind::BufferType));
                    node.validate();
                }
                TokenKind::Literal(Literal::Int(num)) => {
                    global
                        .tokens
                        .expect_next_is(global.errors, &TokenKind::Close(Bracket::Square))?;
                    type_(global, dependencies, node.arg())?;

                    let length = if let Ok(length) = usize::try_from(num) {
                        length
                    } else {
                        global.error(
                            loc,
                            "This number is too big to be the size of an array".to_string(),
                        );
                        return Err(());
                    };

                    node.set(Node::new(loc, NodeKind::ArrayType(length)));
                    node.validate();
                }
                _ => {
                    global.error(loc, "Expected integer or ']'".to_string());
                    return Err(());
                }
            }
        }
        TokenKind::Open(Bracket::Round) => {
            global.tokens.next();
            if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
                node.set(Node::new(
                    loc,
                    NodeKind::LiteralType(TypeKind::Empty.into()),
                ));
                node.validate();
            } else {
                type_(global, dependencies, node)?;
                global
                    .tokens
                    .expect_next_is(global.errors, &TokenKind::Close(Bracket::Round))?;
            }
        }
        TokenKind::Keyword(Keyword::Extern) => {
            global.tokens.next();
            global
                .tokens
                .expect_next_is(global.errors, &TokenKind::Keyword(Keyword::Function))?;
            function_type(global, dependencies, loc, node, true)?;
        }
        TokenKind::Keyword(Keyword::Function) => {
            global.tokens.next();
            function_type(global, dependencies, loc, node, false)?;
        }
        TokenKind::Keyword(Keyword::Bool) => {
            global.tokens.next();
            node.set(Node::new(loc, NodeKind::LiteralType(TypeKind::Bool.into())));
            node.validate();
        }
        TokenKind::Type(type_) => {
            global.tokens.next();
            node.set(Node::new(loc, NodeKind::LiteralType(type_)));
            node.validate();
        }
        TokenKind::PrimitiveInt(type_) => {
            global.tokens.next();
            node.set(Node::new(loc, NodeKind::LiteralType(type_.into())));
            node.validate();
        }
        _ => {
            if global.tokens.try_consume_operator_string("&").is_some() {
                type_(global, dependencies, node.arg())?;
                node.set(Node::new(loc, NodeKind::ReferenceType));
                node.validate();
            } else {
                global.error(
                    loc,
                    "Unexpected token, expected type expression".to_string(),
                );
                return Err(());
            }
        }
    }

    Ok(())
}

/// A value without unary operators, member accesses, or anything like that.
fn atom_value(
    global: &mut DataContext<'_>,
    imperative: &mut ImperativeContext<'_>,
    mut node: NodeBuilder<'_>,
) -> Result<(), ()> {
    {
        let mut arg_node = node.arg();
        let token = global.tokens.expect_next(global.errors)?;
        match token.kind {
            TokenKind::Identifier(name) => {
                if let Some(local_id) = imperative.get_local(name) {
                    arg_node.set(Node::new(token.loc, NodeKind::Local(local_id)));
                    arg_node.validate();
                } else {
                    imperative
                        .dependencies
                        .add(token.loc, name, DependencyKind::Type);
                    arg_node.set(Node::new(token.loc, NodeKind::Global(name)));
                    arg_node.validate();
                }
            }
            TokenKind::Literal(literal) => {
                arg_node.set(Node::new(token.loc, NodeKind::Literal(literal)));
                arg_node.validate();
            }
            TokenKind::Keyword(Keyword::While) => {
                expression(global, imperative, arg_node.arg())?;
                value(global, imperative, arg_node.arg())?;
                arg_node.set(Node::new(token.loc, NodeKind::While));
                arg_node.validate();
            }
            TokenKind::Keyword(Keyword::If) => {
                expression(global, imperative, arg_node.arg())?;
                value(global, imperative, arg_node.arg())?;

                let has_else;
                if global
                    .tokens
                    .try_consume(&TokenKind::Keyword(Keyword::Else))
                {
                    value(global, imperative, arg_node.arg())?;
                    has_else = true;
                } else {
                    has_else = false;
                }

                arg_node.set(Node::new(token.loc, NodeKind::If { has_else }));
                arg_node.validate();
            }
            TokenKind::Keyword(Keyword::Uninit) => {
                arg_node.set(Node::new(token.loc, NodeKind::Uninit));
                arg_node.validate();
            }
            TokenKind::Keyword(Keyword::Function) => {
                function_declaration(global, imperative.dependencies, arg_node, token.loc)?;
            }
            TokenKind::Keyword(Keyword::BitCast) => {
                value(global, imperative, arg_node.arg())?;
                arg_node.set(Node::new(token.loc, NodeKind::BitCast));
                arg_node.validate();
            }
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

                    expression(global, imperative, arg_node.arg())?;

                    arg_node.set(Node::new(token.loc, NodeKind::Declare(id)));
                    arg_node.validate();
                } else {
                    global.error(token.loc, "Expected identifier".to_string());
                    return Err(());
                }
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
                        arg_node.set(Node::new(
                            loc,
                            NodeKind::Extern {
                                library_name: library_path,
                                symbol_name,
                            },
                        ));
                        arg_node.validate();
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
                let mut n_args = 0;
                loop {
                    if global
                        .tokens
                        .try_consume(&TokenKind::Close(Bracket::Square))
                    {
                        break;
                    }

                    expression(global, imperative, arg_node.arg())?;
                    n_args += 1;

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

                arg_node.set(Node::new(token.loc, NodeKind::ArrayLiteral(n_args)));
                arg_node.validate();
            }
            TokenKind::Open(Bracket::Round) => {
                let mut has_comma = false;
                loop {
                    if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
                        break;
                    }

                    expression(global, imperative, arg_node.arg())?;

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
                    // arg_node.set(Node::new(token.loc, NodeKind::Tuple));
                    // arg_node.validate();
                    todo!("Tuples");
                } else {
                    // Just a parenthesis
                    arg_node.into_arg();
                }
            }

            TokenKind::Open(Bracket::Curly) => {
                imperative.push_scope_boundary();

                loop {
                    if let Some(loc) = global
                        .tokens
                        .try_consume_with_data(&TokenKind::Close(Bracket::Curly))
                    {
                        arg_node.arg().set(Node::new(loc, NodeKind::Empty));
                        break;
                    }

                    expression(global, imperative, arg_node.arg())?;

                    let token = global.tokens.expect_next(global.errors)?;
                    match token.kind {
                        TokenKind::Operator(c) if c == "=" => {
                            // Assignment!
                            expression(global, imperative, arg_node.arg())?;
                            arg_node.collapse(Node::new(token.loc, NodeKind::Assign), 2);

                            global
                                .tokens
                                .expect_next_is(global.errors, &TokenKind::SemiColon)?;
                        }
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
                arg_node.set(Node::new(token.loc, NodeKind::Block));
                arg_node.validate();
            }

            _ => {
                global.error(
                    token.loc,
                    format!("Unexpected token '{:?}', expected value", token.kind),
                );
                return Err(());
            }
        }
    }

    while let Some(loc) = global
        .tokens
        .try_consume_with_data(&TokenKind::Open(Bracket::Round))
    {
        let mut n_args = 0;

        loop {
            if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
                break;
            }

            expression(global, imperative, node.arg())?;
            n_args += 1;

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

        if n_args >= crate::MAX_FUNCTION_ARGUMENTS {
            global.error(
                loc,
                format!(
                    "There can at most be {} arguments in a function",
                    crate::MAX_FUNCTION_ARGUMENTS
                ),
            );
            return Err(());
        }

        node.collapse(Node::new(loc, NodeKind::FunctionCall), n_args + 1);
    }

    node.into_arg();

    Ok(())
}

fn function_type(
    global: &mut DataContext<'_>,
    dependencies: &mut DependencyList,
    loc: Location,
    mut node: NodeBuilder<'_>,
    is_extern: bool,
) -> Result<(), ()> {
    // We start with a list of arguments.
    global
        .tokens
        .expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;

    loop {
        if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
            break;
        }

        type_(global, dependencies, node.arg())?;

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
        type_(global, dependencies, node.arg())?;
    } else {
        node.arg().set(Node::new(
            loc,
            NodeKind::LiteralType(TypeKind::Empty.into()),
        ));
    }

    node.set(Node::new(loc, NodeKind::FunctionType { is_extern }));
    node.validate();

    Ok(())
}

/// Parses a function declaration, although doesn't expect the 'fn' keyword to be included because
/// that keyword was what triggered this function to be called in the first place.
fn function_declaration(
    global: &mut DataContext<'_>,
    dependencies: &mut DependencyList,
    mut node: NodeBuilder<'_>,
    loc: Location,
) -> Result<(), ()> {
    global
        .tokens
        .expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;

    let mut imperative = ImperativeContext::new(dependencies);
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

            type_(global, imperative.dependencies, node.arg())?;
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
        type_(global, imperative.dependencies, node.arg())?;
    } else {
        node.arg().set(Node::new(
            global.tokens.loc(),
            NodeKind::LiteralType(TypeKind::Empty.into()),
        ));
    }

    expression(global, &mut imperative, node.arg())?;

    node.set(Node::new(
        loc,
        NodeKind::FunctionDeclaration {
            locals: imperative.locals,
        },
    ));
    node.validate();

    Ok(())
}
