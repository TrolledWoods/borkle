use crate::dependencies::{DependencyKind, DependencyList};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::locals::LocalVariables;
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::parser::{self, ast::NodeKind as ParserNodeKind};
use crate::program::constant::ConstantRef;
use crate::program::Program;
use crate::types::{IntTypeKind, Type, TypeData, TypeKind};
use ast::{Node, NodeKind};

type ParsedAst = bump_tree::Tree<parser::ast::Node>;
type ParsedNode<'a> = bump_tree::Node<'a, parser::ast::Node>;

pub type Ast = bump_tree::Tree<Node>;
type NodeBuilder<'a> = bump_tree::NodeBuilder<'a, Node>;

pub mod ast;

struct Context<'a> {
    errors: &'a mut ErrorCtx,
    program: &'a Program,
    locals: LocalVariables,
    deps: &'a mut DependencyList,
}

pub fn process_ast(
    errors: &mut ErrorCtx,
    program: &Program,
    locals: LocalVariables,
    ast: &ParsedAst,
) -> Result<(DependencyList, LocalVariables, Ast), ()> {
    let root = ast.root().unwrap();
    let mut ast = Ast::new();
    let mut deps = DependencyList::new();
    let mut ctx = Context {
        errors,
        program,
        locals,
        deps: &mut deps,
    };
    type_ast(&mut ctx, None, &root, ast.builder())?;
    ast.set_root();
    let locals = ctx.locals;
    Ok((deps, locals, ast))
}

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
        ParserNodeKind::Literal(Literal::Float(num)) => match wanted_type.map(Type::kind) {
            Some(TypeKind::F32) => {
                let bytes = (num as f32).to_bits().to_le_bytes();
                type_ = Type::new(TypeKind::F32);

                node.set(Node::new(
                    parsed.loc,
                    NodeKind::Constant(ctx.program.insert_buffer(type_, bytes.as_ptr())),
                    type_,
                ));
                node.validate();
            }
            Some(TypeKind::F64) => {
                let bytes = num.to_bits().to_le_bytes();
                type_ = Type::new(TypeKind::F64);

                node.set(Node::new(
                    parsed.loc,
                    NodeKind::Constant(ctx.program.insert_buffer(type_, bytes.as_ptr())),
                    type_,
                ));
                node.validate();
            }
            Some(wanted_type) => {
                ctx.errors.error(
                    parsed.loc,
                    format!("Expected '{}', found float", wanted_type),
                );
                return Err(());
            }
            None => {
                ctx.errors.error(
                    parsed.loc,
                    "A float literal has to know what type it's supposed to be, consider adding a type bound to it.".to_string(),
                );
                return Err(());
            }
        },
        ParserNodeKind::Literal(Literal::String(ref data)) => {
            let u8_type = Type::new(TypeKind::Int(IntTypeKind::U8));
            type_ = Type::new(TypeKind::Buffer(u8_type));
            let ptr = ctx.program.insert_buffer(
                type_,
                &crate::types::BufferRepr {
                    ptr: data.as_ptr() as *mut _,
                    length: data.len(),
                } as *const _ as *const _,
            );
            node.set(Node::new(parsed.loc, NodeKind::Constant(ptr), type_));
            node.validate();
        }
        ParserNodeKind::ArrayLiteral(len) => {
            let mut element_type = None;
            for child in parsed.children() {
                element_type = Some(type_ast(ctx, element_type, &child, node.arg())?);
            }

            match element_type {
                Some(element_type) => type_ = Type::new(TypeKind::Array(element_type, len)),
                None => match wanted_type {
                    Some(wanted_type) => type_ = wanted_type,
                    None => {
                        ctx.errors.error(parsed.loc, "Because this is an empty array, the types of the elements cannot be inferred; you have to specify a type bound".to_string());
                        return Err(());
                    }
                },
            }

            node.set(Node::new(parsed.loc, NodeKind::ArrayLiteral(len), type_));
            node.validate();
        }
        ParserNodeKind::While => {
            type_ = Type::new(TypeKind::Empty);

            let mut children = parsed.children();

            let condition_node = children.next().unwrap();
            type_ast(
                ctx,
                Some(Type::new(TypeKind::Bool)),
                &condition_node,
                node.arg(),
            )?;

            type_ast(ctx, None, &children.next().unwrap(), node.arg())?;

            node.set(Node::new(parsed.loc, NodeKind::While, type_));
            node.validate();
        }
        ParserNodeKind::If { has_else: false } => {
            type_ = Type::new(TypeKind::Empty);

            let mut children = parsed.children();

            let condition_node = children.next().unwrap();
            type_ast(
                ctx,
                Some(Type::new(TypeKind::Bool)),
                &condition_node,
                node.arg(),
            )?;

            type_ast(ctx, Some(type_), &children.next().unwrap(), node.arg())?;

            node.set(Node::new(
                parsed.loc,
                NodeKind::If { has_else: false },
                type_,
            ));
            node.validate();
        }
        ParserNodeKind::If { has_else: true } => {
            let mut children = parsed.children();

            let condition_node = children.next().unwrap();
            type_ast(
                ctx,
                Some(Type::new(TypeKind::Bool)),
                &condition_node,
                node.arg(),
            )?;

            let true_body_type = type_ast(ctx, wanted_type, &children.next().unwrap(), node.arg())?;
            let false_body_type = type_ast(
                ctx,
                Some(true_body_type),
                &children.next().unwrap(),
                node.arg(),
            )?;

            if true_body_type != false_body_type {
                ctx.errors.error(
                    parsed.loc,
                    format!("Both the if and the else body have to return the same type. The if body has type '{}' while the else body has type '{}'", true_body_type, false_body_type),
                );
                return Err(());
            }

            type_ = true_body_type;

            node.set(Node::new(
                parsed.loc,
                NodeKind::If { has_else: true },
                type_,
            ));
            node.validate();
        }
        ParserNodeKind::Assign => {
            let mut children = parsed.children();
            type_ = Type::new(TypeKind::Empty);

            let to_type = type_ast(ctx, None, &children.next().unwrap(), node.arg())?;
            type_ast(ctx, Some(to_type), &children.next().unwrap(), node.arg())?;

            node.set(Node::new(parsed.loc, NodeKind::Assign, type_));
            node.validate();
        }
        ParserNodeKind::Uninit => {
            if let Some(wanted_type) = wanted_type {
                type_ = wanted_type;
                node.set(Node::new(parsed.loc, NodeKind::Uninit, wanted_type));
                node.validate();
            } else {
                ctx.errors.error(
                    parsed.loc,
                    "Type has to be known at this point; put a type bound on this!".to_string(),
                );
                return Err(());
            }
        }
        ParserNodeKind::FunctionDeclaration { ref locals } => {
            let mut locals = locals.clone();
            let mut children = parsed.children();
            let n_arguments = children.len() - 2;

            let mut arg_types = Vec::new();
            for (local, node) in locals.iter_mut().zip(children.by_ref().take(n_arguments)) {
                let arg_type = const_fold_type_expr(ctx, &node)?;
                local.type_ = Some(arg_type);
                arg_types.push(arg_type);
            }

            let return_type = const_fold_type_expr(ctx, &children.next().unwrap())?;

            type_ = Type::new(TypeKind::Function {
                args: arg_types,
                returns: return_type,
                is_extern: false,
            });

            let mut sub_ctx = Context {
                errors: ctx.errors,
                program: ctx.program,
                // FIXME: Remove the clone here; This should be doable by recursing over an owned
                // version of the tree in the future.
                locals,
                deps: ctx.deps,
            };

            type_ast(
                &mut sub_ctx,
                Some(return_type),
                &children.next().unwrap(),
                node.arg(),
            )?;

            node.set(Node::new(
                parsed.loc,
                NodeKind::FunctionDeclaration {
                    locals: sub_ctx.locals,
                },
                type_,
            ));
            node.validate();
        }
        ParserNodeKind::BitCast => {
            if let Some(casting_to) = wanted_type {
                let mut children = parsed.children();
                let parsed_casting = children.next().unwrap();
                let casting_from = type_ast(ctx, None, &parsed_casting, node.arg())?;

                if casting_from.size() != casting_to.size() {
                    ctx.errors.error(parsed.loc, format!("Cannot bit_cast from '{}' to '{}', the sizes of the types have to be the same.", casting_from, casting_to));
                    return Err(());
                }

                if casting_from == casting_to {
                    ctx.errors.warning(
                        parsed.loc,
                        "Unnecessary bit_cast, the types are the same".to_string(),
                    );
                }

                type_ = casting_to;

                node.set(Node::new(parsed.loc, NodeKind::BitCast, type_));
                node.validate();
            } else {
                ctx.errors.error(parsed.loc, "Can only cast if the type we cast to is known; add a type bound after the cast to tell it what to cast to".to_string());
                return Err(());
            }
        }
        ParserNodeKind::FunctionCall => {
            let mut children = parsed.children();
            let ptr_child = children.next().unwrap();
            let ptr = type_ast(ctx, None, &ptr_child, node.arg())?;
            if let TypeKind::Function {
                args,
                returns,
                is_extern,
            } = ptr.kind()
            {
                if args.len() != children.len() {
                    ctx.errors.error(ptr_child.loc, format!("Function is of type '{}', which has {} arguments, but {} arguments were given in the call", ptr, args.len(), children.len()));
                    return Err(());
                }

                for (&wanted, got) in args.iter().zip(children) {
                    type_ast(ctx, Some(wanted), &got, node.arg())?;
                }

                type_ = *returns;
                node.set(Node::new(
                    ptr_child.loc,
                    NodeKind::FunctionCall {
                        is_extern: *is_extern,
                    },
                    type_,
                ));
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
                if let TypeKind::Function {
                    args: _,
                    returns: _,
                    is_extern: true,
                } = wanted_type.kind()
                {
                    match ctx.program.load_extern_library(
                        library_name,
                        symbol_name.as_str().into(),
                        wanted_type,
                    ) {
                        Ok(func) => {
                            type_ = wanted_type;
                            node.set(Node::new(
                                parsed.loc,
                                NodeKind::Constant(ctx.program.insert_buffer(
                                    wanted_type,
                                    &(func as usize) as *const usize as *const _,
                                )),
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
                        "Only extern function pointer types can be imported from external sources"
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
            Some(TypeKind::Int(int)) => {
                let bytes = num.to_le_bytes();

                if !int.range().contains(&(num as i128)) {
                    let range = int.range();
                    ctx.errors.error(
                            parsed.loc,
                            format!("Given integer does not fit within a '{:?}', only values from {} to {} fit in this integer", int, range.start(), range.end())
                        );
                    return Err(());
                }

                type_ = (*int).into();
                node.set(Node::new(
                    parsed.loc,
                    NodeKind::Constant(ctx.program.insert_buffer(type_, bytes.as_ptr())),
                    type_,
                ));
                node.validate();
            }
            Some(wanted_type) => {
                ctx.errors.error(
                    parsed.loc,
                    format!("Expected '{}', found integer", wanted_type),
                );
                return Err(());
            }
            None => {
                ctx.errors.error(
                    parsed.loc,
                    "An integer literal has to know what type it's supposed to be, consider adding a type bound to it.".to_string(),
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

            type_ = const_fold_type_expr(ctx, &type_expr)?;
            type_ast(ctx, Some(type_), &internal, node)?;
        }
        ParserNodeKind::Binary(op) => {
            let mut children = parsed.children();
            let left = children.next().unwrap();
            let right = children.next().unwrap();

            match op {
                BinaryOp::And | BinaryOp::Or => {
                    type_ = Type::new(TypeKind::Bool);
                    type_ast(ctx, Some(type_), &left, node.arg())?;
                    type_ast(ctx, Some(type_), &right, node.arg())?;
                }
                BinaryOp::Equals
                | BinaryOp::NotEquals
                | BinaryOp::LargerThanEquals
                | BinaryOp::LargerThan
                | BinaryOp::LessThanEquals
                | BinaryOp::LessThan => {
                    type_ = Type::new(TypeKind::Bool);
                    let left_type = type_ast(ctx, None, &left, node.arg())?;
                    type_ast(ctx, Some(left_type), &right, node.arg())?;
                }
                BinaryOp::Add | BinaryOp::Sub => {
                    let left_type = type_ast(ctx, wanted_type, &left, node.arg())?;

                    match left_type.kind() {
                        TypeKind::Int(_) | TypeKind::F32 | TypeKind::F64 => {
                            type_ast(ctx, Some(left_type), &right, node.arg())?;
                            type_ = left_type;
                        }
                        TypeKind::Reference(_) => {
                            type_ast(
                                ctx,
                                Some(Type::new(TypeKind::Int(IntTypeKind::Usize))),
                                &right,
                                node.arg(),
                            )?;

                            type_ = left_type;
                        }
                        _ => {
                            ctx.errors.error(
                                parsed.loc,
                                format!(
                                    "No overload takes type '{}' as left hand operand",
                                    left_type
                                ),
                            );
                            return Err(());
                        }
                    }
                }
                BinaryOp::Mult | BinaryOp::Div | BinaryOp::BitAnd | BinaryOp::BitOr => {
                    let left_type = type_ast(ctx, wanted_type, &left, node.arg())?;
                    let right_type = type_ast(ctx, Some(left_type), &right, node.arg())?;

                    if left_type != right_type {
                        ctx.errors
                            .error(parsed.loc, "Operands do not have the same type".to_string());
                        return Err(());
                    }

                    type_ = left_type;
                }
            }

            node.set(Node::new(parsed.loc, NodeKind::Binary(op), type_));
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
                UnaryOp::AutoCast => {
                    if let Some(wanted_type) = wanted_type {
                        let internal_type =
                            type_ast(ctx, None, &parsed.children().next().unwrap(), node.arg())?;

                        auto_cast(ctx, parsed.loc, internal_type, wanted_type, node)?;
                        type_ = wanted_type;
                    } else {
                        ctx.errors.error(parsed.loc, "Casting can only be done if the type is known; are you sure you want to cast here?".to_string());
                        return Err(());
                    }
                }
                UnaryOp::Reference => {
                    let wanted_inner =
                        if let Some(&TypeKind::Reference(inner)) = wanted_type.map(Type::kind) {
                            Some(inner)
                        } else {
                            None
                        };

                    let operand = type_ast(ctx, wanted_inner, &operand, node.arg())?;
                    type_ = Type::new(TypeKind::Reference(operand));

                    node.set(Node::new(parsed.loc, NodeKind::Unary(op), type_));
                    node.validate();
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

                    node.set(Node::new(parsed.loc, NodeKind::Unary(op), type_));
                    node.validate();
                }
                _ => {
                    type_ = type_ast(ctx, wanted_type, &operand, node.arg())?;

                    node.set(Node::new(parsed.loc, NodeKind::Unary(op), type_));
                    node.validate();
                }
            }
        }
        ParserNodeKind::Empty => {
            type_ = TypeKind::Empty.into();
            node.set(Node::new(
                parsed.loc,
                NodeKind::Constant(ConstantRef::dangling()),
                type_,
            ));
            node.validate();
        }
        ParserNodeKind::Block { label, ref defers } => {
            if let Some(label) = label {
                let label = ctx.locals.get_label_mut(label);
                label.type_ = wanted_type;
            }

            let mut children = parsed.children();

            let n_children = children.len();
            assert!(n_children > 0);

            for child in children.by_ref().take(n_children - 1) {
                type_ast(ctx, None, &child, node.arg())?;
            }

            type_ = type_ast(ctx, wanted_type, &children.next().unwrap(), node.arg())?;

            let mut typed_defers = Vec::with_capacity(defers.len());
            for defer in defers {
                let mut ast = Ast::new();
                type_ast(ctx, None, &defer.root().unwrap(), ast.builder())?;
                ast.set_root();

                typed_defers.push(ast);
            }

            if let Some(label) = label {
                let label = ctx.locals.get_label_mut(label);
                if let Some(label_type) = label.type_ {
                    if label_type != type_ {
                        ctx.errors.error(parsed.loc, format!("This blocks label has been determined to be of type '{}', but you passed '{}'", label_type, type_));
                        return Err(());
                    }
                } else {
                    label.type_ = Some(type_);
                }
            }

            node.set(Node::new(
                parsed.loc,
                NodeKind::Block {
                    label,
                    defers: typed_defers,
                },
                type_,
            ));
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
        ParserNodeKind::Global(name) => {
            let id = ctx.program.get_member_id(name).unwrap();
            type_ = ctx.program.get_type_of_member(id);
            node.set(Node::new(parsed.loc, NodeKind::Global(id), type_));
            node.validate();
            ctx.deps.add(
                parsed.loc,
                ctx.program.member_name(id),
                DependencyKind::Value,
            );
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
            node.set(Node::new(parsed.loc, NodeKind::Declare(local), type_));
            node.validate();
        }
        ParserNodeKind::TypeAsValue => {
            let mut children = parsed.children();
            let inner_type = const_fold_type_expr(ctx, &children.next().unwrap())?;
            type_ = Type::new(TypeKind::Type);
            node.set(Node::new(
                parsed.loc,
                NodeKind::Constant(ctx.program.insert_buffer(
                    type_,
                    &(inner_type.as_ptr() as usize).to_le_bytes() as *const _,
                )),
                type_,
            ));
            node.validate();
        }
        ParserNodeKind::LiteralType(_)
        | ParserNodeKind::ArrayType(_)
        | ParserNodeKind::StructType(_)
        | ParserNodeKind::FunctionType { .. }
        | ParserNodeKind::BufferType
        | ParserNodeKind::ReferenceType => {
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

fn const_fold_type_expr(ctx: &mut Context<'_>, parsed: &ParsedNode<'_>) -> Result<Type, ()> {
    match parsed.kind {
        ParserNodeKind::Global(name) => {
            let id = ctx.program.get_member_id(name).unwrap();
            let ptr = ctx.program.get_value_of_member(id).as_ptr();
            Ok(unsafe { *ptr.cast::<Type>() })
        }
        ParserNodeKind::LiteralType(type_) => Ok(type_),
        ParserNodeKind::StructType(ref field_names) => {
            let mut fields = Vec::with_capacity(field_names.len());
            for (&name, child) in field_names.iter().zip(parsed.children()) {
                let field_type = const_fold_type_expr(ctx, &child)?;
                fields.push((name, field_type));
            }
            Ok(Type::new(TypeKind::Struct(fields)))
        }
        ParserNodeKind::BufferType => {
            let mut children = parsed.children();
            let pointee = const_fold_type_expr(ctx, &children.next().unwrap())?;
            Ok(TypeKind::Buffer(pointee).into())
        }
        ParserNodeKind::ArrayType(length) => {
            let mut children = parsed.children();
            let member = const_fold_type_expr(ctx, &children.next().unwrap())?;
            Ok(TypeKind::Array(member, length).into())
        }
        ParserNodeKind::ReferenceType => {
            let mut children = parsed.children();
            let pointee = const_fold_type_expr(ctx, &children.next().unwrap())?;
            Ok(TypeKind::Reference(pointee).into())
        }
        ParserNodeKind::FunctionType { is_extern } => {
            let mut children = parsed.children();
            let n_args = children.len() - 1;

            let mut arg_types = Vec::with_capacity(n_args);
            for arg in children.by_ref().take(n_args) {
                arg_types.push(const_fold_type_expr(ctx, &arg)?);
            }

            let returns = const_fold_type_expr(ctx, &children.next().unwrap())?;

            Ok(TypeKind::Function {
                args: arg_types,
                returns,
                is_extern,
            }
            .into())
        }
        _ => {
            ctx.errors.error(
                parsed.loc,
                "This is not a valid type expression(possible internal compiler error, because the parser should have a special state for parsing type expressions and that should not generate an invalid node that the const type expression thing can't handle)"
                    .to_string(),
            );
            Err(())
        }
    }
}

/// Creates an auto cast. The 'node' is expected to have an argument which is the node whom we cast
/// from.
fn auto_cast(
    ctx: &mut Context<'_>,
    loc: Location,
    from_type: Type,
    to_type: Type,
    mut node: NodeBuilder<'_>,
) -> Result<(), ()> {
    if from_type == to_type {
        node.into_arg();
        ctx.errors.warning(
            loc,
            format!(
                "You don't need a cast here, because '{}' and '{}' are the same types",
                from_type, to_type
            ),
        );
        return Ok(());
    }

    match (from_type.kind(), to_type.kind()) {
        (
            TypeKind::Reference(Type(TypeData {
                kind: TypeKind::Array(from_inner, len),
                ..
            })),
            TypeKind::Buffer(to_inner),
        ) if from_inner == to_inner => {
            node.set(Node::new(loc, NodeKind::ArrayToBuffer(*len), to_type));
            node.validate();
            Ok(())
        }
        (TypeKind::Reference(_), TypeKind::Int(IntTypeKind::Usize)) => {
            node.set(Node::new(loc, NodeKind::BitCast, to_type));
            node.validate();
            Ok(())
        }
        (
            TypeKind::Reference(Type(TypeData {
                kind: TypeKind::Array(from_inner, _),
                ..
            })),
            TypeKind::Reference(to_inner),
        ) if from_inner == to_inner => {
            node.set(Node::new(loc, NodeKind::BitCast, to_type));
            node.validate();
            Ok(())
        }
        (_, _) => {
            ctx.errors.error(
                loc,
                format!("No cast available for '{}' to '{}'", from_type, to_type),
            );
            Err(())
        }
    }
}
