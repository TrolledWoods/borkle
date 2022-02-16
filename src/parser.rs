use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::locals::{Local, LocalVariables, LabelId, LocalId, LocalScopeId, Polymorphic, PolymorphicId};
use crate::location::Location;
use crate::operators::{BinaryOp, Operator, UnaryOp};
use crate::program::{Program, ScopeId, Task, BuiltinFunction, constant::ConstantRef, MemberMetaData, MemberId, MemberKind, PolyOrMember, Builtin};
use std::sync::Arc;
use crate::types::{Type, TypeKind};
use context::{DataContext, ImperativeContext};
use lexer::{Bracket, Keyword, Token, TokenKind};
use std::path::{Path, PathBuf};
use std::fmt;
use ustr::Ustr;

use crate::ast::{self, AstStructure, AstBuilder, NodeId, FinishedNode};

pub type NodeView<'a>    = ast::GenericNodeView<'a, &'a [Node]>;
pub type NodeViewMut<'a> = ast::GenericNodeView<'a, &'a mut [Node]>;

mod context;
mod lexer;
mod token_stream;

type AstSlot<'a> = ast::AstSlot<'a, Vec<Node>>;
type Muncher<'a> = ast::Muncher<'a, Vec<Node>>;

#[derive(Debug, Clone)]
pub struct Ast {
    pub name: Ustr,
    pub structure: AstStructure,
    pub nodes: Vec<Node>,
}

impl Ast {
    fn from_builder(name: Ustr, builder: AstBuilder<Vec<Node>>) -> Self {
        let (structure, nodes) = builder.finish();
        Self {
            name,
            structure,
            nodes,
        }
    }

    pub fn root_id(&self) -> NodeId {
        self.structure.root_id()
    }

    pub fn root(&self) -> NodeView<'_> {
        self.structure.root(&self.nodes[..])
    }

    pub fn root_mut(&mut self) -> NodeViewMut<'_> {
        self.structure.root(&mut self.nodes[..])
    }

    pub fn get(&self, id: NodeId) -> NodeView<'_> {
        self.structure.get(id, &self.nodes[..])
    }

    pub fn get_mut(&mut self, id: NodeId) -> NodeViewMut<'_> {
        self.structure.get(id, &mut self.nodes[..])
    }
}

pub fn process_string(
    errors: &mut ErrorCtx,
    program: &Program,
    file: Ustr,
    string: &str,
    scope: ScopeId,
) -> Result<u64, ()> {
    profile::profile!("process_string");

    let (mut tokens, loc) = lexer::process_string(errors, file, string)?;

    let mut context = DataContext::new(errors, program, &mut tokens, Path::new(&*file), scope);

    let mut no_base = None;
    parse_basic_tags(
        &mut context,
        "file header",
        &mut [("no_base".into(), &mut no_base)]
    )?;

    if no_base.is_none() {
        program.add_file_from_import(
            offset_path(&context.program.arguments.lib_path, "base.bo"),
            context.tokens.loc(),
            context.scope,
            true,
        );
    }

    while let Some(token) = context.tokens.peek() {
        // @Hack: Workaround for the borrowing errors
        let token = token.clone();

        match token.kind {
            TokenKind::Keyword(Keyword::Type) => {
                context.tokens.next();
                type_declaration(&mut context)?;
            }
            TokenKind::Keyword(Keyword::Const) => {
                context.tokens.next();
                constant(&mut context)?;
            }
            TokenKind::Keyword(Keyword::Library) => {
                context.tokens.next();
                let name = context.tokens.expect_next(context.errors)?;
                if let TokenKind::StringLiteral(name) = name.kind {
                    context
                        .tokens
                        .expect_next_is(context.errors, &TokenKind::SemiColon)?;

                    let path = offset_path(&context.program.arguments.lib_path, &name);

                    program.add_file_from_import(path, token.loc, context.scope, true);
                } else {
                    context.error(
                        name.loc,
                        "Expected string literal for file name".to_string(),
                    );
                    return Err(());
                }
            }
            TokenKind::Keyword(Keyword::Import) => {
                context.tokens.next();

                let name = context.tokens.expect_next(context.errors)?;
                if let TokenKind::StringLiteral(name) = name.kind {
                    context
                        .tokens
                        .expect_next_is(context.errors, &TokenKind::SemiColon)?;

                    let mut path = context.path.to_path_buf();
                    path.pop();
                    let path = offset_path(&path, &name);

                    program.add_file_from_import(path, token.loc, context.scope, false);
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
                let tree = Ast::from_builder("__anonymous__".into(), buffer);

                let id = context
                    .program
                    .define_member(context.errors, token.loc, None, "<anonymous>".into(), MemberKind::Const)?;

                context.program.queue_task(
                    dependencies,
                    Task::TypeMember { member_id: id, locals, ast: tree, member_kind: MemberKind::Const },
                );

                context
                    .tokens
                    .expect_next_is(context.errors, &TokenKind::SemiColon)?;
            }
        }
    }

    Ok(loc)
}

fn type_declaration(global: &mut DataContext) -> Result<(), ()> {
    let mut is_aliased = None;
    let mut is_builtin = None;
    parse_basic_tags(global, "type declaration", &mut [("alias".into(), &mut is_aliased), ("builtin".into(), &mut is_builtin)])?;

    let (loc, name) = global.tokens.expect_identifier(global.errors)?;

    let mut buffer = AstBuilder::new();

    let mut dependencies = DependencyList::new();
    let mut locals = LocalVariables::new();
    let mut imperative = ImperativeContext::new(
        &mut dependencies,
        &mut locals,
        false,
        &[],
    );

    let mut root = buffer.add();
    let poly_args = parse_polymorphic_arguments(global, &mut imperative, &mut root)?;

    if global.tokens.try_consume_operator_string("=").is_none() {
        global.error(loc, "Expected '=' after type".to_string());
        return Err(());
    }

    type_(global, &mut imperative, root.add())?;
    root.finish(Node::new(loc, NodeKind::TypeCreator));

    let tree = Ast::from_builder(name, buffer);

    let id = if poly_args.is_empty() {
        let id = global
            .program
            .define_member(global.errors, loc, Some(global.scope), name, MemberKind::Type { is_aliased: is_aliased.is_some() })?;
        global.program.queue_task(
            dependencies,
            Task::TypeMember { member_id: id, locals, ast: tree, member_kind: MemberKind::Type { is_aliased: is_aliased.is_some() }},
        );

        PolyOrMember::Member(id)
    } else {
        let id = global.program.define_polymorphic_member(
            global.errors,
            loc,
            global.scope,
            name,
            poly_args.iter().map(|v| extract_name(&locals, tree.get(v.node_id))).collect(),
            MemberKind::Type { is_aliased: is_aliased.is_some() },
        )?;
        global.program.queue_task(
            dependencies.clone(),
            Task::TypePolyMember {
                member_id: id,
                locals,
                ast: tree,
                dependencies,
                poly_args,
                member_kind: MemberKind::Type { is_aliased: is_aliased.is_some() },
            },
        );

        PolyOrMember::Poly(id)
    };

    if let Some(_) = is_builtin {
        if let Some(builtin) = Builtin::builtin_type_from_string(name.as_str()) {
            global.program.bind_member_to_builtin(global.errors, builtin, loc, id)?;
        } else {
            global.errors.error(loc, format!("No builtin with the name `{}`", name));
            return Err(());
        }
    }

    global
        .tokens
        .expect_next_is(global.errors, &TokenKind::SemiColon)?;

    Ok(())
}

fn constant(global: &mut DataContext) -> Result<(), ()> {
    let token = global.tokens.expect_next(global.errors)?;
    if let TokenKind::Identifier(name) = token.kind {
        let mut dependencies = DependencyList::new();
        let mut locals = LocalVariables::new();
        let mut imperative = ImperativeContext::new(
            &mut dependencies,
            &mut locals,
            false,
            &[],
        );

        let mut buffer = AstBuilder::new();
        let mut root = buffer.add();

        let poly_args = parse_polymorphic_arguments(global, &mut imperative, &mut root)?;

        if let Some(_) = global.tokens.try_consume_operator_string(":") {
            type_(global, &mut imperative, root.add())?;
        } else {
            root.add().finish(Node::new(token.loc, NodeKind::ImplicitType));
        }

        if global.tokens.try_consume_operator_string("=").is_none() {
            global.error(token.loc, "Expected '=' after const".to_string());
            return Err(());
        }

        expression(global, &mut imperative, root.add())?;

        root.finish(Node::new(token.loc, NodeKind::ConstCreator));

        let tree = Ast::from_builder(name, buffer);

        if poly_args.is_empty() {
            let id = global
                .program
                .define_member(global.errors, token.loc, Some(global.scope), name, MemberKind::Const)?;
            global.program.queue_task(
                dependencies,
                Task::TypeMember { member_id: id, locals, ast: tree, member_kind: MemberKind::Const },
            );
        } else {
            let id = global.program.define_polymorphic_member(
                global.errors,
                token.loc,
                global.scope,
                name,
                poly_args.iter().map(|v| extract_name(&locals, tree.get(v.node_id))).collect(),
                MemberKind::Const,
            )?;
            global.program.queue_task(
                dependencies.clone(),
                Task::TypePolyMember {
                    member_id: id,
                    locals,
                    ast: tree,
                    dependencies,
                    poly_args,
                    member_kind: MemberKind::Const,
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
    global: &mut DataContext,
    imperative: &mut ImperativeContext<'_>,
    slot: AstSlot<'_>,
) -> Result<FinishedNode, ()> {
    let expr = expression_rec(global, imperative, slot, 0)?;

    Ok(expr)
}

fn expression_rec(
    global: &mut DataContext,
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
            muncher.munch(2, Node::new(loc, NodeKind::TypeBound));
        } else if op == BinaryOp::Is {
            type_(global, imperative, muncher.add())?;
            muncher.munch(2, Node::new(loc, NodeKind::Is));
        } else {
            expression_rec(global, imperative, muncher.add(), op.precedence())?;
            muncher.munch(2, Node::new(loc, NodeKind::Binary { op }));
        }
    }

    Ok(muncher.finish())
}

fn type_(
    global: &mut DataContext,
    imperative: &mut ImperativeContext<'_>,
    mut slot: AstSlot<'_>,
) -> Result<FinishedNode, ()> {
    let token = global.tokens.expect_peek(global.errors)?;
    let loc = token.loc;
    match token.kind {
        TokenKind::Keyword(Keyword::Any) => {
            global.tokens.next();

            imperative.push_scope_boundary();

            // TODO: `maybe_parse_polymorphic_arguments` should just add things to the scope.
            let arguments = maybe_parse_polymorphic_arguments(global)?;
            if arguments.is_empty() {
                global.errors.error(loc, format!("`any` needs at least one generic argument"));
                return Err(());
            }

            for (loc, name) in arguments {
                let id = imperative.insert_poly(Polymorphic::new(loc, name));
                slot.add().finish(Node::new(loc, NodeKind::DeclPolyArgument(id)));
            }

            type_(global, imperative, slot.add())?;
            imperative.pop_scope_boundary();

            Ok(slot.finish(Node::new(loc, NodeKind::Any)))
        }
        TokenKind::Keyword(Keyword::Int) => {
            global.tokens.next();
            Ok(slot.finish(Node::new(loc, NodeKind::IntType)))
        }
        TokenKind::Keyword(Keyword::TypeOf) => {
            global.tokens.next();

            // @TODO: We want to tell the parser about
            // the fact that we don't actually need the values of anything
            // in here, so that it doesn't fetch them unnecessarily
            let old_in_declarative_lvalue = imperative.in_declarative_lvalue;
            let old_in_template_declaration = imperative.in_template_declaration;
            imperative.in_declarative_lvalue = false;
            value(global, imperative, slot.add())?;
            imperative.in_declarative_lvalue = old_in_declarative_lvalue;
            imperative.in_template_declaration = old_in_template_declaration;

            Ok(slot.finish(Node::new(loc, NodeKind::TypeOf)))
        }
        TokenKind::Identifier(name) => {
            global.tokens.next();

            let mut muncher = slot.into_muncher();

            if let Some(local_scope_id) = imperative.get_local(name) {
                match local_scope_id {
                    LocalScopeId::Local(id) => {
                        let local = imperative.locals.get(id);
                        global.errors.info(local.loc, format!("Defined here"));
                        global.errors.error(loc, format!("`{}` is a local variable, not a type (did you intend to add `typeof`?)", name));
                        return Err(());
                    }
                    LocalScopeId::Polymorphic(id) => {
                        muncher.add().finish(Node::new(loc, NodeKind::PolymorphicArgumentNew(id)));
                    }
                    LocalScopeId::Label(id) => {
                        let poly = imperative.locals.get_label(id);
                        global.errors.info(poly.loc, format!("Defined here"));
                        global.errors.error(loc, format!("`{}` is a label, not a type", name));
                        return Err(());
                    }
                }
            } else if let Some(index) = imperative
                .poly_args
                .iter()
                .position(|(_, arg)| *arg == name)
            {
                muncher.add().finish(Node::new(loc, NodeKind::PolymorphicArgument(index)));
            } else {
                imperative.dependencies.add(
                    loc,
                    DepKind::MemberByName(
                        global.scope,
                        name,
                        MemberDep::Type,
                    ),
                );
                muncher.add().finish(Node::new(
                    loc,
                    NodeKind::Global { scope: global.scope, name },
                ));
            }

            // @Copypasta from value_without_unaries.
            while let Some(&Token { ref kind, loc, .. }) = global.tokens.peek() {
                match kind {
                    TokenKind::Operator(string) if string.as_str() == "." => {
                        global.tokens.next();

                        let token = global.tokens.expect_next(global.errors)?;
                        match token.kind {
                            TokenKind::Open(Bracket::Round) => {
                                let old_evaluate_at_typing = imperative.evaluate_at_typing;
                                let old_declarative_lvalue = imperative.in_declarative_lvalue;
                                imperative.evaluate_at_typing = true;
                                imperative.in_declarative_lvalue = false;
                                let count = function_arguments(global, imperative, &mut muncher)?;
                                imperative.evaluate_at_typing = old_evaluate_at_typing;
                                imperative.in_declarative_lvalue = old_declarative_lvalue;

                                muncher.munch(count + 1, Node::new(loc, NodeKind::PolymorphicArgs));
                            }
                            _ => {
                                global.error(token.loc, "Expected a generic argument list".to_string());
                                return Err(());
                            }
                        }
                    }
                    _ => break,
                }
            }

            Ok(muncher.finish())
        }
        TokenKind::Keyword(Keyword::Underscore) => {
            global.tokens.next();

            Ok(slot.finish(Node::new(loc, NodeKind::ImplicitType)))
        }
        TokenKind::Keyword(Keyword::Enum) => {
            global.tokens.next();

            type_(global, imperative, slot.add())?;

            global.tokens.expect_next_is(global.errors, &TokenKind::Open(Bracket::Curly))?;

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

                if global.tokens.try_consume_operator_string("=").is_none() {
                    global.error(
                        global.tokens.loc(),
                        "Expected '=' for enum field value".to_string(),
                    );
                    return Err(());
                }

                expression(global, imperative, slot.add())?;
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

            Ok(slot.finish(Node::new(loc, NodeKind::EnumType { fields })))
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

            Ok(slot.finish(Node::new(loc, NodeKind::StructType { fields })))
        }
        TokenKind::Open(Bracket::Square) => {
            global.tokens.next();
            match global.tokens.expect_peek(global.errors)?.kind {
                TokenKind::Close(Bracket::Square) => {
                    global.tokens.next();

                    type_(global, imperative, slot.add())?;
                    Ok(slot.finish(Node::new(loc, NodeKind::BufferType)))
                }
                _ => {
                    let old_evaluate_at_typing = imperative.evaluate_at_typing;
                    let old_in_declarative_lvalue = imperative.in_declarative_lvalue;
                    imperative.evaluate_at_typing = true;
                    imperative.in_declarative_lvalue = false;
                    expression(global, imperative, slot.add())?;
                    global
                        .tokens
                        .expect_next_is(global.errors, &TokenKind::Close(Bracket::Square))?;
                    imperative.evaluate_at_typing = old_evaluate_at_typing;
                    imperative.in_declarative_lvalue = old_in_declarative_lvalue;
                    type_(global, imperative, slot.add())?;

                    Ok(slot.finish(Node::new(
                        loc,
                        NodeKind::ArrayType,
                    )))
                }
            }
        }
        TokenKind::Open(Bracket::Round) => {
            global.tokens.next();

            let has_to_be_tuple = loop {
                if global
                    .tokens
                    .try_consume(&TokenKind::Close(Bracket::Round))
                {
                    break true;
                }

                type_(global, imperative, slot.add())?;

                let token = global.tokens.expect_next(global.errors)?;
                match token.kind {
                    TokenKind::Close(Bracket::Round) => break false,
                    TokenKind::Comma => {}
                    _ => {
                        global.error(token.loc, "Expected either ',' or ']'".to_string());
                        return Err(());
                    }
                }
            };

            if slot.num_children() == 1 && !has_to_be_tuple {
                Ok(slot.finish(Node::new(loc, NodeKind::Parenthesis)))
            } else if slot.num_children() == 0 {
                // Temporary! We want to replace `Empty` with an empty tuple later on
                Ok(slot.finish(Node::new(
                    loc,
                    NodeKind::LiteralType(TypeKind::Empty.into()),
                )))
            } else {
                Ok(slot.finish(Node::new(loc, NodeKind::TupleType)))
            }
        }
        TokenKind::Keyword(Keyword::Function) => {
            global.tokens.next();
            function_type(global, imperative, loc, slot)
        }
        TokenKind::Keyword(Keyword::Bool) => {
            global.tokens.next();
            Ok(slot.finish(Node::new(loc, NodeKind::LiteralType(TypeKind::Bool.into()))))
        }
        TokenKind::Type(ref type_) => {
            let type_ = type_.clone();
            global.tokens.next();
            Ok(slot.finish(Node::new(loc, NodeKind::LiteralType(type_))))
        }
        TokenKind::PrimitiveInt(type_) => {
            global.tokens.next();
            Ok(slot.finish(Node::new(loc, NodeKind::LiteralType(type_.into()))))
        }
        _ => {
            if global.tokens.try_consume_operator_string("&").is_some() {
                type_(global, imperative, slot.add())?;
                Ok(slot.finish(Node::new(loc, NodeKind::ReferenceType)))
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
    global: &mut DataContext,
    imperative: &mut ImperativeContext<'_>,
    mut slot: AstSlot<'_>,
) -> Result<FinishedNode, ()> {
    if let Some((loc, op)) = global.tokens.try_consume_operator() {
        if op == UnaryOp::Reference {
            value(global, imperative, slot.add())?;
            Ok(slot.finish(Node::new(loc, NodeKind::Reference)))
        } else if op == UnaryOp::Range {
            Ok(slot.finish(Node::new(loc, NodeKind::LeaveToBeInferred)))
        } else if op == UnaryOp::Member {
            let (_, name) = global.tokens.expect_identifier(global.errors)?;
            Ok(slot.finish(Node::new(loc, NodeKind::AnonymousMember { name })))
        } else {
            value(global, imperative, slot.add())?;
            Ok(slot.finish(Node::new(loc, NodeKind::Unary { op })))
        }
    } else {
        value_without_unaries(global, imperative, slot)
    }
}

/// A value
fn value_without_unaries(
    global: &mut DataContext,
    imperative: &mut ImperativeContext<'_>,
    base_slot: AstSlot<'_>,
) -> Result<FinishedNode, ()> {
    let mut muncher = base_slot.into_muncher();
    let token = global.tokens.expect_next(global.errors)?;
    let loc = token.loc;

    let mut slot = muncher.add();
    match token.kind {
        TokenKind::Keyword(Keyword::TypeOf) => {
            // @TODO: We want to tell the parser about
            // the fact that we don't actually need the values of anything
            // in here, so that it doesn't fetch them unnecessarily
            value(global, imperative, slot.add())?;

            slot.finish(Node::new(loc, NodeKind::TypeOf))
        }
        TokenKind::Keyword(Keyword::Underscore) => {
            slot.finish(Node::new(token.loc, NodeKind::ImplicitType))
        }
        TokenKind::Keyword(Keyword::Let) => {
            if imperative.in_declarative_lvalue {
                global.error(token.loc, format!("Cannot use `let` when already inside of a declarative lvalue"));
                return Err(());
            }

            imperative.in_declarative_lvalue = true;
            expression_rec(global, imperative, slot.add(), 2)?;
            imperative.in_declarative_lvalue = false;

            slot.finish(Node::new(
                loc,
                NodeKind::Declare,
            ))
        }
        TokenKind::Identifier(name) => {
            if imperative.in_declarative_lvalue {
                let local_id = imperative.insert_local(Local::new(token.loc, name));
                slot.finish(Node::new(token.loc, NodeKind::Local { local_id }))
            } else if imperative.in_template_declaration {
                let id = imperative.insert_poly(Polymorphic::new(token.loc, name));
                slot.finish(Node::new(token.loc, NodeKind::DeclPolyArgument(id)))
            } else {
                if let Some(local_id) = imperative.get_local(name) {
                    match local_id {
                        LocalScopeId::Local(local_id) => {
                            let local = imperative.locals.get_mut(local_id);
                            local.num_uses += 1;
                            local.uses.push(token.loc);
                            slot.finish(Node::new(token.loc, NodeKind::Local { local_id }))
                        }
                        // TODO: Copy paste!
                        LocalScopeId::Polymorphic(id) => {
                            slot.finish(Node::new(token.loc, NodeKind::PolymorphicArgumentNew(id)))
                        }
                        LocalScopeId::Label(id) => {
                            let poly = imperative.locals.get_label(id);
                            global.errors.info(poly.loc, format!("Defined here"));
                            global.errors.error(loc, format!("`{}` is a label, not a local variable", name));
                            return Err(());
                        }
                    }
                } else if let Some(index) = imperative
                    .poly_args
                    .iter()
                    .position(|(_, arg)| *arg == name)
                {
                    slot.finish(Node::new(token.loc, NodeKind::PolymorphicArgument(index)))
                } else {
                    imperative.dependencies.add(
                        token.loc,
                        DepKind::MemberByName(
                            global.scope,
                            name,
                            if imperative.evaluate_at_typing { MemberDep::ValueAndCallableIfFunction } else { MemberDep::Type },
                        ),
                    );
                    slot.finish(Node::new(
                        token.loc,
                        NodeKind::Global { scope: global.scope, name },
                    ))
                }
            }
        }
        TokenKind::IntLiteral(literal) => slot.finish(Node::new(token.loc, NodeKind::IntLiteral(literal))),
        TokenKind::CharLiteral(literal) => slot.finish(Node::new(token.loc, NodeKind::CharLiteral(literal))),
        TokenKind::FloatLiteral(literal) => slot.finish(Node::new(token.loc, NodeKind::FloatLiteral(literal))),
        TokenKind::StringLiteral(literal) => slot.finish(Node::new(token.loc, NodeKind::StringLiteral(literal))),
        TokenKind::ArrayStringLiteral(literal) => {
            slot.finish(Node::new(token.loc, NodeKind::ArrayStringLiteral(literal)))
        }
        TokenKind::CStringLiteral(literal) => {
            imperative.dependencies.add(
                loc,
                DepKind::MemberByBuiltin(
                    Builtin::CString,
                    MemberDep::Type,
                ),
            );

            slot.finish(Node::new(token.loc, NodeKind::CStringLiteral(literal)))
        }
        TokenKind::Keyword(Keyword::BuiltinFunction) => {
            let (name_loc, name) = global.tokens.expect_identifier(global.errors)?;

            let builtin_kind = match name.as_str() {
                "create_exe" => BuiltinFunction::CreateExe,
                "create_bir" => BuiltinFunction::CreateBir,
                "assert" => BuiltinFunction::Assert,
                "mem_copy" => BuiltinFunction::MemCopy,
                "mem_copy_nonoverlapping" => BuiltinFunction::MemCopyNonOverlapping,
                "alloc" => BuiltinFunction::Alloc,
                "dealloc" => BuiltinFunction::Dealloc,
                "stdout_write" => BuiltinFunction::StdoutWrite,
                "stdout_flush" => BuiltinFunction::StdoutFlush,
                "stdin_read" => BuiltinFunction::StdinRead,
                _ => {
                    global.error(
                        name_loc,
                        format!("'{}' doesn't correspond to any built in function", name),
                    );
                    return Err(());
                }
            };

            slot.finish(Node::new(
                token.loc,
                NodeKind::BuiltinFunction(builtin_kind),
            ))
        }
        TokenKind::Keyword(Keyword::Pack) => {
            // TODO: I probably want an expression here, but I need a way to define these kinds of
            // "unary" operations to use expressions without going crazy, so we need some check to
            // make sure these themselves aren't inside of an expression.
            value(global, imperative, slot.add())?;
            slot.finish(Node::new(
                token.loc,
                NodeKind::Pack,
            ))
        }
        TokenKind::Keyword(Keyword::Unpack) => {
            // TODO: See `Pack`
            value(global, imperative, slot.add())?;
            slot.finish(Node::new(
                token.loc,
                NodeKind::Unpack,
            ))
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
                slot.finish(Node::new(token.loc, NodeKind::ConstAtTyping))
            } else {
                slot.finish(Node::new(token.loc, NodeKind::ConstAtEvaluation))
            }
        }
        TokenKind::Keyword(Keyword::SizeOf) => {
            type_(global, imperative, slot.add())?;
            slot.finish(Node::new(token.loc, NodeKind::SizeOf))
        }
        TokenKind::Keyword(Keyword::Explain) => {
            expression(global, imperative, slot.add())?;

            slot.finish(Node::new(
                token.loc,
                NodeKind::Explain,
            ))
        }
        TokenKind::Keyword(Keyword::Type) => {
            type_(global, imperative, slot.add())?;
            slot.finish(Node::new(token.loc, NodeKind::TypeAsValue))
        }
        TokenKind::PrimitiveInt(type_) => {
            slot.add().finish(Node::new(token.loc, NodeKind::LiteralType(type_.into())));
            slot.finish(Node::new(token.loc, NodeKind::TypeAsValue))
        }
        TokenKind::Keyword(Keyword::Break) => {
            let id = if global.tokens.try_consume(&TokenKind::SingleQuote) {
                let (loc, label_name) = global.tokens.expect_identifier(global.errors)?;

                match imperative.get_local(label_name) {
                    Some(LocalScopeId::Label(id)) => id,
                    _ => {
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
                slot.add().finish(Node::new(loc, NodeKind::Empty));
            } else {
                expression(global, imperative, slot.add())?;
            }

            let label_mut = imperative.locals.get_label_mut(id);
            if label_mut.first_break_location.is_none() {
                label_mut.first_break_location = Some(loc);
            }

            slot.finish(Node::new(
                token.loc,
                NodeKind::Break {
                    label: id,
                    num_defer_deduplications,
                },
            ))
        }
        TokenKind::Keyword(Keyword::For) => {
            imperative.push_scope_boundary();

            let mut is_const = None;
            parse_basic_tags(global, "for", &mut [("const".into(), &mut is_const)])?;

            let label = parse_default_label(global, imperative)?;

            let locals_count = imperative.get_local_count();

            let iterator_local = if let Some(Token {
                kind: TokenKind::Keyword(Keyword::In),
                ..
            }) = global.tokens.peek_nth(1)
            {
                let (name_loc, name) = global.tokens.expect_identifier(global.errors)?;
                global.tokens.next();

                Local::new(name_loc, name)
            } else {
                Local::new(token.loc, "v".into())
            };
            let iterator = imperative.insert_local(iterator_local.read_only());
            let iteration_var = imperative.insert_local(Local::new(token.loc, "i".into()).read_only());

            expression(global, imperative, slot.add())?;

            imperative.whitelist_locals(locals_count);

            slot.add().finish(Node::new(loc, NodeKind::Local { local_id: iteration_var }));

            let mut for_inner = slot.add();
            for_inner.add().finish(Node::new(loc, NodeKind::Local { local_id: iterator }));

            expression(global, imperative, for_inner.add())?;

            for_inner.finish(Node::new(loc, NodeKind::ForInner));

            imperative.pop_default_label();
            imperative.pop_scope_boundary();

            if global
                .tokens
                .try_consume(&TokenKind::Keyword(Keyword::Else))
            {
                expression(global, imperative, slot.add())?;
            } else {
                slot.add().finish(Node::new(loc, NodeKind::Empty));
            }

            slot.finish(Node::new(
                token.loc,
                NodeKind::For {
                    is_const,
                    label,
                },
            ))
        }
        TokenKind::Keyword(Keyword::While) => {
            imperative.push_scope_boundary();
            let label = parse_default_label(global, imperative)?;

            let locals_count = imperative.get_local_count();
            let iteration_var = imperative.insert_local(Local::new(token.loc, "i".into()).read_only());
            imperative.whitelist_locals(locals_count);

            slot.add().finish(Node::new(loc, NodeKind::Local { local_id: iteration_var }));

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
                slot.add().finish(Node::new(loc, NodeKind::Empty));
            }

            slot.finish(Node::new(
                token.loc,
                NodeKind::While {
                    label,
                },
            ))
        }
        TokenKind::Keyword(Keyword::If) => {
            // Parse tags
            let found_tags = parse_tags(global, imperative, slot.add())?;
            // Condition
            if (found_tags & tags::COMPILE) > 0 {
                let old = imperative.evaluate_at_typing;
                imperative.evaluate_at_typing = true;
                expression(global, imperative, slot.add())?;
                imperative.evaluate_at_typing = old;
            } else {
                expression(global, imperative, slot.add())?;
            }

            expression(global, imperative, slot.add())?;

            if global
                .tokens
                .try_consume(&TokenKind::Keyword(Keyword::Else))
            {
                expression(global, imperative, slot.add())?;
            } else {
                slot.add().finish(Node::new(loc, NodeKind::Empty));
            }

            slot.finish(Node::new(
                token.loc,
                NodeKind::If,
            ))
        }
        TokenKind::Keyword(Keyword::Uninit) => slot.finish(Node::new(token.loc, NodeKind::Uninit)),
        TokenKind::Keyword(Keyword::Zeroed) => slot.finish(Node::new(token.loc, NodeKind::Zeroed)),
        TokenKind::Keyword(Keyword::Function) => {
            function_declaration(global, imperative, slot, token.loc)?
        }
        TokenKind::Keyword(Keyword::Cast) => {
            value(global, imperative, slot.add())?;
            slot.finish(Node::new(token.loc, NodeKind::Cast))
        }
        TokenKind::Keyword(Keyword::BitCast) => {
            value(global, imperative, slot.add())?;
            slot.finish(Node::new(token.loc, NodeKind::BitCast))
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

            slot.finish(Node::new(token.loc, NodeKind::ArrayLiteral))
        }
        TokenKind::Open(Bracket::Round) => {
            let has_to_be_tuple = loop {
                if global
                    .tokens
                    .try_consume(&TokenKind::Close(Bracket::Round))
                {
                    break true;
                }

                expression(global, imperative, slot.add())?;

                let token = global.tokens.expect_next(global.errors)?;
                match token.kind {
                    TokenKind::Close(Bracket::Round) => break false,
                    TokenKind::Comma => {}
                    _ => {
                        global.error(token.loc, "Expected either ',' or ']'".to_string());
                        return Err(());
                    }
                }
            };

            if slot.num_children() == 1 && !has_to_be_tuple {
                slot.finish(Node::new(token.loc, NodeKind::Parenthesis))
            } else {
                slot.finish(Node::new(token.loc, NodeKind::Tuple))
            }
        }

        TokenKind::Open(Bracket::Curly) => {
            imperative.push_scope_boundary();

            parse_tags(global, imperative, slot.add())?;

            let label = maybe_parse_label(global, imperative)?;

            loop {
                if let Some(loc) = global
                    .tokens
                    .try_consume_with_data(&TokenKind::Close(Bracket::Curly))
                {
                    slot.add().finish(Node::new(loc, NodeKind::Empty));
                    break;
                }

                let local_count = imperative.get_local_count();

                let peek_token = global.tokens.expect_peek(global.errors)?;
                let loc = peek_token.loc;
                match peek_token.kind {
                    TokenKind::Keyword(Keyword::Defer) => {
                        global.tokens.next();

                        let mut defer_node = slot.add();
                        expression(global, imperative, defer_node.add())?;
                        defer_node.finish(Node::new(loc, NodeKind::Defer));

                        imperative.defer_depth += 1;

                        if let Some(label) = label {
                            imperative.locals.get_label_mut(label).num_defers += 1;
                        }
                    }
                    _ => {
                        expression(global, imperative, slot.add())?;
                    }
                }

                imperative.whitelist_locals(local_count);

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
            slot.finish(Node::new(token.loc, NodeKind::Block { label }))
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
            TokenKind::Operator(string) if string.as_str() == "->" => {
                global.tokens.next();

                let (global_loc, name) = global.tokens.expect_identifier(global.errors)?;
                // TODO: We want to support generic arguments on the identifier

                muncher.add().finish(Node::new(global_loc, NodeKind::Global { scope: global.scope, name }));

                if global.tokens.try_consume_operator_string(".").is_some() {
                    global.tokens.expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;
                    let old_evaluate_at_typing = imperative.evaluate_at_typing;
                    imperative.evaluate_at_typing = true;
                    let count = function_arguments(global, imperative, &mut muncher)?;
                    imperative.evaluate_at_typing = old_evaluate_at_typing;

                    muncher.munch(count + 1, Node::new(loc, NodeKind::PolymorphicArgs));
                }

                imperative.dependencies.add(
                    token.loc,
                    DepKind::MemberByName(
                        global.scope,
                        name,
                        if imperative.evaluate_at_typing { MemberDep::ValueAndCallableIfFunction } else { MemberDep::Type },
                    ),
                );

                global.tokens.expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;
                let count = function_arguments(global, imperative, &mut muncher)?;
                muncher.munch(count + 2, Node::new(loc, NodeKind::ExpressiveFunctionCall));
            }
            TokenKind::Operator(string) if string.as_str() == "." => {
                global.tokens.next();

                let token = global.tokens.expect_next(global.errors)?;
                match token.kind {
                    TokenKind::Identifier(name) => {
                        muncher.munch(1, Node::new(loc, NodeKind::Member { name }));
                    }
                    TokenKind::Open(Bracket::Round) => {
                        let old_evaluate_at_typing = imperative.evaluate_at_typing;
                        imperative.evaluate_at_typing = true;
                        let count = function_arguments(global, imperative, &mut muncher)?;
                        imperative.evaluate_at_typing = old_evaluate_at_typing;

                        muncher.munch(count + 1, Node::new(loc, NodeKind::PolymorphicArgs));
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
                muncher.munch(count + 1, Node::new(loc, NodeKind::FunctionCall));
            }
            _ => break,
        }
    }

    Ok(muncher.finish())
}

fn function_type(
    global: &mut DataContext,
    imperative: &mut ImperativeContext<'_>,
    loc: Location,
    mut slot: AstSlot<'_>,
) -> Result<FinishedNode, ()> {
    parse_tags(global, imperative, slot.add())?;

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
        slot.add().finish(Node::new(
            loc,
            NodeKind::LiteralType(TypeKind::Empty.into()),
        ));
    };

    Ok(slot.finish(Node::new(loc, NodeKind::FunctionType)))
}

fn function_arguments(
    global: &mut DataContext,
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
    global: &mut DataContext,
    imperative: &mut ImperativeContext<'_>,
    mut slot: AstSlot<'_>,
    loc: Location,
) -> Result<FinishedNode, ()> {
    parse_tags(global, imperative, slot.add())?;

    global
        .tokens
        .expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;

    imperative.push_scope_boundary();

    let mut argument_infos = Vec::new();
    loop {
        if global.tokens.try_consume(&TokenKind::Close(Bracket::Round)) {
            break;
        }

        let mut argument_info = FunctionArgumentInfo::default();
        parse_basic_tags(
            global,
            "function argument",
            &mut [
                ("var_args".into(), &mut argument_info.var_args)
            ],
        )?;

        argument_infos.push(argument_info);

        let locals_count = imperative.get_local_count();

        let old = imperative.in_declarative_lvalue;
        imperative.in_declarative_lvalue = true;
        expression_rec(global, imperative, slot.add(), 1)?;
        imperative.in_declarative_lvalue = old;

        imperative.whitelist_locals(locals_count);

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
        slot.add().finish(Node::new(loc, NodeKind::ImplicitType));
    }

    let is_extern = if global.tokens.try_consume(&TokenKind::Keyword(Keyword::Extern)) {
        let Token { kind: TokenKind::StringLiteral(message), .. } = global.tokens.expect_next(global.errors)? else {
            global.error(loc, "Expected string literal after `extern`".to_string());
            return Err(());
        };
        
        Some(message.into())
    } else {
        None
    };

    if is_extern.is_none() {
        expression(global, imperative, slot.add())?;
    }

    imperative.pop_scope_boundary();

    Ok(slot.finish(Node::new(
        loc,
        NodeKind::FunctionDeclaration {
            is_extern,
            argument_infos,
        },
    )))
}

#[derive(Debug, Clone)]
pub struct PolyArgumentInfo {
    pub is_const: Option<Location>,
    pub node_id: NodeId,
    pub loc: Location,
}

fn parse_polymorphic_arguments(
    global: &mut DataContext,
    imperative: &mut ImperativeContext<'_>,
    slot: &mut AstSlot<'_>,
) -> Result<Vec<PolyArgumentInfo>, ()> {
    let old_in_template_declaration = imperative.in_template_declaration;
    imperative.in_template_declaration = true;

    let mut args = Vec::new();

    if global.tokens.try_consume_operator_string(".").is_some() {
        global.tokens.expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;

        loop {
            if global
                .tokens
                .try_consume(&TokenKind::Close(Bracket::Round))
            {
                break;
            }

            let mut is_const = None;

            parse_basic_tags(global, "polymorphic argument", &mut [
                ("const".into(), &mut is_const)
            ])?;

            let loc = global.tokens.loc();
            let expr = expression(global, imperative, slot.add())?;
            args.push(PolyArgumentInfo {
                is_const,
                loc,
                node_id: expr.id,
            });

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

    imperative.in_template_declaration = old_in_template_declaration;

    Ok(args)
}

fn maybe_parse_polymorphic_arguments(
    global: &mut DataContext,
) -> Result<Vec<(Location, Ustr)>, ()> {
    let mut args = Vec::new();

    if global.tokens.try_consume_operator_string(".").is_some() {
        global.tokens.expect_next_is(global.errors, &TokenKind::Open(Bracket::Round))?;

        loop {
            if global
                .tokens
                .try_consume(&TokenKind::Close(Bracket::Round))
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
    global: &mut DataContext,
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
            declared_at: None,
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
    global: &mut DataContext,
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
                declared_at: None,
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

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum TagKind {
    CallingConvention,
    Target,
    Compile,
    Label(LabelId),
}

pub mod tags {
    pub const CALLING_CONVENTION: u32 = 0x01;
    pub const TARGET:             u32 = 0x02;
    pub const COMPILE:            u32 = 0x04;
    pub const LABEL:              u32 = 0x08;
}   

fn parse_tags(global: &mut DataContext, imperative: &mut ImperativeContext<'_>, mut slot: AstSlot<'_>) -> Result<u32, ()> {
    let loc = global.tokens.loc();

    let mut found_tags = 0;

    let mut is_first = true;
    loop {
        let Some(&Token { loc, kind: TokenKind::Tag(tag_name), .. }) = global.tokens.peek() else {
            if is_first {
                break;
            } else {
                global.error(global.tokens.loc(), format!("You need a `:` after a tag list to close it"));
                return Err(());
            }
        };

        is_first = false;

        global.tokens.next();

        match tag_name.as_str() {
            "call" => {
                let mut tag = slot.add();
                expression_rec(global, imperative, tag.add(), 9)?;
                tag.finish(Node::new(loc, NodeKind::Tag(TagKind::CallingConvention)));

                imperative.dependencies.add(
                    loc,
                    DepKind::MemberByBuiltin(
                        Builtin::CallingConvention,
                        MemberDep::Type,
                    ),
                );

                found_tags |= tags::CALLING_CONVENTION;
            }
            "target" => {
                let mut tag = slot.add();
                expression_rec(global, imperative, tag.add(), 9)?;
                tag.finish(Node::new(loc, NodeKind::Tag(TagKind::Target)));

                imperative.dependencies.add(
                    loc,
                    DepKind::MemberByBuiltin(
                        Builtin::Target,
                        MemberDep::Type,
                    ),
                );

                found_tags |= tags::TARGET;
            }
            // TODO: Rename this to `compile`.
            "const" => {
                slot.add().finish(Node::new(loc, NodeKind::Tag(TagKind::Compile)));

                found_tags |= tags::COMPILE;
            }
            "label" => {
                let (label_loc, name) = global.tokens.expect_identifier(global.errors)?;
                let id = imperative.insert_label(
                    name,
                    crate::locals::Label {
                        loc: label_loc,
                        defer_depth: imperative.defer_depth,
                        first_break_location: None,
                        declared_at: None,
                        stack_frame_id: 0,
                        num_defers: 0,
                        type_: None,
                        value: None,
                        ir_labels: None,
                    },
                );
                slot.add().finish(Node::new(loc, NodeKind::Tag(TagKind::Label(id))));
            }
            _ => {
                global.error(global.tokens.loc(), format!("`{}` is not a tag", tag_name));
                return Err(());
            }
        }

        if global.tokens.try_consume_operator_string(":").is_some() {
            break;
        } else {
            global.tokens.expect_next_is(global.errors, &TokenKind::Comma)?;
        }
    }

    slot.finish(Node::new(loc, NodeKind::TagList { found_tags }));
    Ok(found_tags)
}

// TODO: This could be removed later probably
fn parse_basic_tags(global: &mut DataContext, expr_name: &str, tags: &mut [(Ustr, &mut Option<Location>)]) -> Result<(), ()> {
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

pub fn extract_name(locals: &LocalVariables, node: NodeView<'_>) -> Option<(Ustr, Location)> {
    match node.kind {
        NodeKind::DeclPolyArgument(id) => {
            Some((locals.get_poly(id).name, node.loc))
        }
        NodeKind::Local { local_id, .. } => {
            Some((locals.get(local_id).name, node.loc))
        }
        NodeKind::TypeBound => {
            let [value, _] = node.children.into_array();
            extract_name(locals, value)
        }
        _ => None,
    }
}

fn offset_path(path: &Path, addition: &str) -> PathBuf {
    let mut path = path.to_path_buf();

    for part in addition.split('/') {
        if part == ".." {
            path.pop();
        } else {
            path.push(part);
        }
    }

    path
}

#[derive(Default, Debug, Clone)]
pub struct FunctionArgumentInfo {
    pub var_args: Option<Location>,
}

#[derive(Clone)]
pub struct Node {
    pub loc: Location,
    pub kind: NodeKind,
}

impl Node {
    fn new(loc: Location, kind: NodeKind) -> Self {
        Self {
            loc,
            kind,
        }
    }
}

#[derive(Debug, Clone)]
pub enum NodeKind {
    CharLiteral(u8),
    IntLiteral(i128),
    FloatLiteral(f64),
    StringLiteral(String),
    CStringLiteral(Vec<u8>),
    ArrayStringLiteral(Vec<u8>),
    ArrayLiteral,
    BuiltinFunction(BuiltinFunction),

    /// [ .. poly args, type, expression ]
    ConstCreator,
    /// [ .. poly args, expression ]
    TypeCreator,

    Explain,

    /// [ .. poly args: DeclPolyArgument, inner ]
    Any,
    DeclPolyArgument(PolymorphicId),

    PolymorphicArgumentNew(PolymorphicId),
    PolymorphicArgument(usize),
    ConstAtTyping,
    ConstAtEvaluation,

    /// A list of tags.
    TagList {
        found_tags: u32,
    },
    /// Args depend on TagKind.
    Tag(TagKind),

    Global {
        scope: ScopeId,
        name: Ustr,
    },

    /// [ inner ]
    Pack,
    /// [ inner ]
    Unpack,

    /// [ of, ..args ]
    PolymorphicArgs,

    Constant(ConstantRef, Option<Arc<MemberMetaData>>),
    ResolvedGlobal(MemberId, Arc<MemberMetaData>),

    /// The reason this is separate from `For` is that const for loops
    /// only "polymorph" this part of the for, the rest isn't polymorphed.
    /// [v_value, body]
    ForInner,
    /// [ iterator, i_value, inner: ForInner, else_body ]
    For {
        is_const: Option<Location>,
        label: LabelId,
    },
    /// [ i, condition, body, else_body ]
    While {
        label: LabelId,
    },
    /// [ tags, condition, body, else_body ]
    If,

    AnonymousMember { name: Ustr },
    /// [ of ]
    Member {
        name: Ustr,
    },

    /// [ tags, .. arg, returns, body ]  (at least 2 children)
    FunctionDeclaration {
        is_extern: Option<Ustr>,
        argument_infos: Vec<FunctionArgumentInfo>,
    },

    /// [ inner ]
    TypeOf,
    /// [ inner ]
    SizeOf,
    /// Type expressions actually use the type of the node to mean the type of the expression. So if you were to do
    /// &T, this would have the type &T. This of course, isn't compatible with how normal expressions work, so we
    /// need this node to convert from the way type expressions work to the way values work, by taking the type of the
    /// type expression, inserting it into the global type table, and then making that value a constant. (and the type
    /// is of course `Type`). Except that this isn't the full story, in reality type expressions are what's called
    /// "inferrable constants", which means that if you use a `type`, inside of a type, it just "disappears", and
    /// allows for inferrence through it. This is vital for allowing constants with `type` to behave as you'd expect.
    /// [ inner ]
    TypeAsValue,
    ImplicitType,
    LeaveToBeInferred,
    /// [ .. fields ]
    StructType {
        fields: Vec<Ustr>,
    },
    /// [ base_type, .. fields ]
    EnumType {
        fields: Vec<Ustr>,
    },
    /// no children
    IntType,
    /// no children
    FloatType,
    /// [ len, member ]
    ArrayType,
    /// [ args .. ]
    TupleType,
    /// [ .. args, returns ]
    FunctionType,
    /// [ inner ]
    BufferType,
    /// [ inner ]
    ReferenceType,
    LiteralType(Type),
    /// [ inner ]
    Reference,
    /// [ operand ]
    Unary {
        op: UnaryOp,
    },
    /// [ left, right ]
    Binary {
        op: BinaryOp,
    },
    /// [ expression ]
    Break {
        label: LabelId,
        num_defer_deduplications: usize,
    },
    /// [ inner ]
    Defer,
    /// [ calling, .. args ]
    FunctionCall,
    /// [ calling, .. args ]
    ResolvedFunctionCall {
        arg_indices: Vec<usize>,
    },
    /// [ first_argument, calling, ..args ]
    ExpressiveFunctionCall,
    /// [ tags, .. contents ]
    Block {
        label: Option<LabelId>,
    },
    /// [ inner ]
    Parenthesis,
    /// [ args .. ]
    Tuple,
    Empty,
    Uninit,
    Zeroed,

    /// [ value, wanted_type ]
    Is,
    /// [ value, bound ]
    TypeBound,
    /// [ inner ]
    Cast,
    /// [ inner ]
    BitCast,
    /// [ declaring ]
    Declare,
    Local {
        local_id: LocalId,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum LocalUsage {
    Standard,
    WriteToMember,
    DirectWrite,
}

impl fmt::Debug for Node {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(fmt)
    }
}
