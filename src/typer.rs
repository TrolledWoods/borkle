use crate::dependencies::{DependencyKind, DependencyList};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::locals::LocalVariables;
use crate::operators::UnaryOp;
use crate::parser::{self, ast::NodeKind as ParserNodeKind};
use crate::program::{Function, MemberId, Program};
use crate::types::{Type, TypeKind};
use ast::{Node, NodeKind};
use std::convert::TryFrom;

type ParsedAst = bump_tree::Tree<parser::ast::Node>;
type ParsedNode<'a> = bump_tree::Node<'a, parser::ast::Node>;

pub type Ast = bump_tree::Tree<Node>;
type NodeBuilder<'a> = bump_tree::NodeBuilder<'a, Node>;

pub mod ast;

struct Context<'a> {
    errors: &'a mut ErrorCtx,
    program: &'a Program,
    locals: LocalVariables,
    deps: DependencyList,
}

pub fn process_ast(
    errors: &mut ErrorCtx,
    program: &Program,
    locals: LocalVariables,
    ast: &ParsedAst,
) -> Result<(DependencyList, LocalVariables, Ast), ()> {
    let root = ast.root().unwrap();
    let mut ast = Ast::new();
    let mut ctx = Context {
        errors,
        program,
        locals,
        deps: DependencyList::new(),
    };
    type_ast(&mut ctx, None, &root, ast.builder())?;
    ast.set_root();
    Ok((ctx.deps, ctx.locals, ast))
}

// NOTE: ParsedNode is both Copy and 8 bytes. I don't see why the lint is triggered
// in this case.
/// If the `wanted_type` is Some(type_), this function itself will generate an error if the types
/// do not match, i.e., if Some(type_) is passed as the `wanted_type`, if the function returns Ok
/// that is guaranteed to be the type_ passed in.
#[allow(clippy::needless_pass_by_value)]
fn type_ast(
    ctx: &mut Context<'_>,
    wanted_type: Option<Type>,
    parsed: &ParsedNode<'_>,
    mut node: NodeBuilder<'_>,
) -> Result<Type, ()> {
    let type_: Type;
    match parsed.kind {
        ParserNodeKind::Literal(Literal::String(_)) => todo!(),
        ParserNodeKind::FunctionCall => {
            let mut children = parsed.children();
            let ptr_child = children.next().unwrap();
            let ptr = type_ast(ctx, None, &ptr_child, node.arg())?;
            if let TypeKind::Function { args, returns } = ptr.kind() {
                if args.len() != children.len() {
                    ctx.errors.error(ptr_child.loc, format!("Function is of type '{}', which has {} arguments, but {} arguments were given in the call", ptr, args.len(), children.len()));
                    return Err(());
                }

                for (&wanted, got) in args.iter().zip(children) {
                    type_ast(ctx, Some(wanted), &got, node.arg())?;
                }

                type_ = *returns;
                node.set(Node::new(ptr_child.loc, NodeKind::FunctionCall, type_));
                node.validate();
            } else {
                ctx.errors.error(
                    ptr_child.loc,
                    format!(
                        "Can only call function on function pointer, found type '{}'",
                        ptr
                    ),
                );
                return Err(());
            }
        }
        ParserNodeKind::Extern {
            ref library_name,
            ref symbol_name,
        } => {
            if let Some(wanted_type) = wanted_type {
                if let TypeKind::Function { args, returns } = wanted_type.kind() {
                    let mut libraries = ctx.program.libraries.lock();
                    match libraries.load_symbol(
                        library_name.as_str().into(),
                        symbol_name.as_str().into(),
                        args,
                        *returns,
                    ) {
                        Ok(func) => {
                            let id = ctx.program.insert_function(Function::FFI(func));
                            type_ = wanted_type;
                            node.set(Node::new(
                                parsed.loc,
                                NodeKind::Constant(id.into()),
                                wanted_type,
                            ));
                            node.validate();
                        }
                        Err(err) => {
                            ctx.errors.error(
                                parsed.loc,
                                format!("Failed to load extern symbol\n{:?}", err),
                            );
                            return Err(());
                        }
                    }
                } else {
                    ctx.errors.error(
                        parsed.loc,
                        "Only function pointer types can be imported from external sources"
                            .to_string(),
                    );
                    return Err(());
                }
            } else {
                ctx.errors.error(parsed.loc, "The type has to be known at this point. You can specify the type of the item to import by adding a type bound, ': [type]' after it".to_string());
                return Err(());
            }
        }
        ParserNodeKind::Literal(Literal::Int(num)) => match wanted_type.map(Type::kind) {
            Some(TypeKind::I64) | None => {
                type_ = TypeKind::I64.into();
                node.set(Node::new(parsed.loc, NodeKind::Constant(num.into()), type_));
                node.validate();
            }
            Some(TypeKind::U8) => {
                type_ = TypeKind::U8.into();
                if let Ok(byte) = u8::try_from(num) {
                    node.set(Node::new(
                        parsed.loc,
                        NodeKind::Constant(byte.into()),
                        type_,
                    ));
                    node.validate();
                } else {
                    ctx.errors.error(
                        parsed.loc,
                        "Given integer does not fit within a 'u8', u8 has the range 0-255"
                            .to_string(),
                    );
                    return Err(());
                }
            }
            Some(wanted_type) => {
                ctx.errors.error(
                    parsed.loc,
                    format!("Expected '{}', found integer", wanted_type),
                );
                return Err(());
            }
        },
        ParserNodeKind::TypeBound => {
            let mut children = parsed.children();
            let internal = children.next().unwrap();
            let type_expr = children.next().unwrap();

            if wanted_type.is_some() {
                ctx.errors.warning(
                    parsed.loc,
                    "Unnecessary type bound, the type is already known".to_string(),
                );
            }

            type_ = const_fold_type_expr(ctx.errors, type_expr)?;
            type_ast(ctx, Some(type_), &internal, node)?;
        }
        ParserNodeKind::Binary(op) => {
            let mut children = parsed.children();
            let left = children.next().unwrap();
            let right = children.next().unwrap();

            let left_type = type_ast(ctx, wanted_type, &left, node.arg())?;
            let right_type = type_ast(ctx, Some(left_type), &right, node.arg())?;

            if left_type != right_type {
                ctx.errors
                    .error(parsed.loc, "Operands do not have the same type".to_string());
            }

            type_ = left_type;
            node.set(Node::new(parsed.loc, NodeKind::Binary(op), left_type));
            node.validate();
        }
        ParserNodeKind::Unary(op) => {
            let mut children = parsed.children();
            let operand = children.next().unwrap();

            // FIXME: We want to specify the wanted type more precisely, but it may
            // depend on the operator. Maybe we want to make referencing and dereferencing
            // their own ast nodes, and not have them be unary operators at all, because they
            // are exceptions from the rule that operators return their own type, so they need
            // special treatment. It might be nice to push this complexity out where there is
            // already such difference in behaviour between nodes.
            match op {
                UnaryOp::Reference => {
                    let wanted_inner =
                        if let Some(&TypeKind::Reference(inner)) = wanted_type.map(Type::kind) {
                            Some(inner)
                        } else {
                            None
                        };

                    let operand = type_ast(ctx, wanted_inner, &operand, node.arg())?;
                    type_ = Type::new(TypeKind::Reference(operand));
                }
                UnaryOp::Dereference => {
                    let wanted_inner = wanted_type.map(|v| Type::new(TypeKind::Reference(v)));

                    let operand = type_ast(ctx, wanted_inner, &operand, node.arg())?;
                    if let TypeKind::Reference(inner) = *operand.kind() {
                        type_ = inner;
                    } else {
                        ctx.errors.error(
                            parsed.loc,
                            format!(
                                "Cannot dereference '{}', because it's not a refernece",
                                operand
                            ),
                        );
                        return Err(());
                    }
                }
                _ => {
                    type_ = type_ast(ctx, wanted_type, &operand, node.arg())?;
                }
            }

            node.set(Node::new(parsed.loc, NodeKind::Unary(op), type_));
            node.validate();
        }
        ParserNodeKind::Empty => {
            type_ = TypeKind::Empty.into();
            node.set(Node::new(parsed.loc, NodeKind::Constant(().into()), type_));
            node.validate();
        }
        ParserNodeKind::Block => {
            let mut children = parsed.children();

            let n_children = children.len();
            assert!(n_children > 0);

            for child in children.by_ref().take(n_children - 1) {
                type_ast(ctx, None, &child, node.arg())?;
            }

            type_ = type_ast(ctx, wanted_type, &children.next().unwrap(), node.arg())?;
            node.set(Node::new(parsed.loc, NodeKind::Block, type_));
            node.validate();
        }
        ParserNodeKind::Member(name) => {
            let mut children = parsed.children();
            let child = children.next().unwrap();

            let member_of = type_ast(ctx, None, &child, node.arg())?;

            if let Some(member) = member_of.member(name) {
                type_ = member.type_;

                node.set(Node::new(parsed.loc, NodeKind::Member(name), type_));
                node.validate();
            } else {
                ctx.errors.error(
                    parsed.loc,
                    format!("The type '{}' does not have member '{}'", member_of, name),
                );
                return Err(());
            }
        }
        ParserNodeKind::Global(id) => {
            type_ = ctx.program.get_type_of_member(id).expect("The type of a member should have been made a dependency in the parser, so it should be defined by the time we get here, no matter what.");
            node.set(Node::new(
                parsed.loc,
                NodeKind::Global(MemberId::from_ustr(id)),
                type_,
            ));
            node.validate();
            ctx.deps.add(id, DependencyKind::Value);
        }
        ParserNodeKind::Local(local) => {
            type_ = ctx.locals.get(local).type_.unwrap();
            node.set(Node::new(parsed.loc, NodeKind::Local(local), type_));
        }
        ParserNodeKind::Declare(local) => {
            let mut children = parsed.children();
            let local_type = type_ast(ctx, None, &children.next().unwrap(), node.arg())?;

            ctx.locals.get_mut(local).type_ = Some(local_type);
            type_ = Type::new(TypeKind::Empty);
            node.set(Node::new(parsed.loc, NodeKind::Assign(local), type_));
            node.validate();
        }
        ParserNodeKind::LiteralType(_) | ParserNodeKind::FunctionType => {
            ctx.errors.error(
                parsed.loc,
                "(Internal compiler error) The parser should not emit a type node here".to_string(),
            );
            return Err(());
        }
    }

    if let Some(wanted_type) = wanted_type {
        if wanted_type != type_ {
            ctx.errors.error(
                parsed.loc,
                format!("Expected '{}', found '{}'", wanted_type, type_),
            );
            return Err(());
        }
    }

    Ok(type_)
}

#[allow(clippy::needless_pass_by_value)]
fn const_fold_type_expr(errors: &mut ErrorCtx, parsed: ParsedNode<'_>) -> Result<Type, ()> {
    match parsed.kind {
        ParserNodeKind::LiteralType(type_) => Ok(type_),
        ParserNodeKind::FunctionType => {
            let mut children = parsed.children();
            let n_args = children.len() - 1;

            let mut arg_types = Vec::with_capacity(n_args);
            for arg in children.by_ref().take(n_args) {
                arg_types.push(const_fold_type_expr(errors, arg)?);
            }

            let returns = const_fold_type_expr(errors, children.next().unwrap())?;

            Ok(TypeKind::Function {
                args: arg_types,
                returns,
            }
            .into())
        }
        _ => {
            errors.error(
                parsed.loc,
                "This is not a valid type expression(possible internal compiler error, because the parser should have a special state for parsing type expressions and that should not generate an invalid node that the const type expression thing can't handle)"
                    .to_string(),
            );
            Err(())
        }
    }
}
