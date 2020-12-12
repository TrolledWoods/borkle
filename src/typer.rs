use crate::dependencies::{DependencyKind, DependencyList};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::locals::LocalVariables;
use crate::location::Location;
use crate::operators::UnaryOp;
use crate::parser::ast::Node as ParsedNode;
use crate::parser::{self, ast::NodeKind as ParsedNodeKind, Ast as ParsedAst};
use crate::program::constant::ConstantRef;
use crate::program::Program;
use crate::types::{IntTypeKind, Type, TypeData, TypeKind};
use ast::{Node, NodeKind};

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
    parsed: &ParsedAst,
) -> Result<(DependencyList, LocalVariables, Ast), ()> {
    let mut ast = Ast::new();
    let mut deps = DependencyList::new();
    let mut ctx = Context {
        errors,
        program,
        locals,
        deps: &mut deps,
    };
    type_ast(&mut ctx, None, parsed, ast.builder())?;
    ast.set_root();
    let locals = ctx.locals;
    Ok((deps, locals, ast))
}

/// If the `wanted_type` is Some(type_), this function itself will generate an error if the types
/// do not match, i.e., if Some(type_) is passed as the `wanted_type`, if the function returns Ok
/// that is guaranteed to be the type_ passed in.
fn type_ast<'a>(
    ctx: &mut Context<'a>,
    wanted_type: Option<Type>,
    parsed: &'a ParsedNode,
    mut node: NodeBuilder<'_>,
) -> Result<Type, ()> {
    let type_: Type;
    match parsed.kind {
        ParsedNodeKind::Defer { ref deferring } => {
            let mut typed_ast = Ast::new();
            type_ast(ctx, None, deferring, typed_ast.builder())?;
            typed_ast.set_root();
            type_ = Type::new(TypeKind::Empty);

            node.set(Node::new(
                parsed.loc,
                NodeKind::Defer(Box::new(typed_ast)),
                type_,
            ));
            node.validate();
        }
        ParsedNodeKind::Literal(Literal::Float(num)) => match wanted_type.map(Type::kind) {
            Some(TypeKind::F32) => {
                // FIXME: Maybe we want a compiler error for when num is truncated?
                #[allow(clippy::cast_possible_truncation)]
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
        ParsedNodeKind::Literal(Literal::String(ref data)) => {
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
        ParsedNodeKind::ArrayLiteral(ref elements) => {
            let mut element_type = None;
            for element in elements {
                element_type = Some(type_ast(ctx, element_type, element, node.arg())?);
            }

            match element_type {
                Some(element_type) => {
                    type_ = Type::new(TypeKind::Array(element_type, elements.len()))
                }
                None => match wanted_type {
                    Some(wanted_type) => type_ = wanted_type,
                    None => {
                        ctx.errors.error(parsed.loc, "Because this is an empty array, the types of the elements cannot be inferred; you have to specify a type bound".to_string());
                        return Err(());
                    }
                },
            }

            node.set(Node::new(
                parsed.loc,
                NodeKind::ArrayLiteral(elements.len()),
                type_,
            ));
            node.validate();
        }
        ParsedNodeKind::While {
            ref condition,
            ref body,
        } => {
            type_ = Type::new(TypeKind::Empty);

            type_ast(ctx, Some(Type::new(TypeKind::Bool)), condition, node.arg())?;
            type_ast(ctx, None, body, node.arg())?;

            node.set(Node::new(parsed.loc, NodeKind::While, type_));
            node.validate();
        }
        ParsedNodeKind::If {
            ref condition,
            ref true_body,
            false_body: None,
        } => {
            type_ = Type::new(TypeKind::Empty);

            type_ast(ctx, Some(Type::new(TypeKind::Bool)), condition, node.arg())?;
            type_ast(ctx, Some(type_), true_body, node.arg())?;

            node.set(Node::new(
                parsed.loc,
                NodeKind::If { has_else: false },
                type_,
            ));
            node.validate();
        }
        ParsedNodeKind::If {
            ref condition,
            ref true_body,
            false_body: Some(ref false_body),
        } => {
            type_ast(ctx, Some(Type::new(TypeKind::Bool)), condition, node.arg())?;

            let true_body_type = type_ast(ctx, wanted_type, true_body, node.arg())?;
            let false_body_type = type_ast(ctx, Some(true_body_type), false_body, node.arg())?;

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
        ParsedNodeKind::Assign {
            ref lvalue,
            ref rvalue,
        } => {
            type_ = Type::new(TypeKind::Empty);

            let to_type = type_ast(ctx, None, lvalue, node.arg())?;
            type_ast(ctx, Some(to_type), rvalue, node.arg())?;

            node.set(Node::new(parsed.loc, NodeKind::Assign, type_));
            node.validate();
        }
        ParsedNodeKind::Uninit => {
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
        ParsedNodeKind::FunctionDeclaration {
            ref locals,
            ref args,
            ref returns,
            ref body,
        } => {
            let mut locals = locals.clone();

            let mut arg_types = Vec::new();
            for (local, node) in locals.iter_mut().zip(args) {
                let arg_type = const_fold_type_expr(ctx, node)?;
                local.type_ = Some(arg_type);
                arg_types.push(arg_type);
            }

            let return_type = const_fold_type_expr(ctx, returns)?;

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

            type_ast(&mut sub_ctx, Some(return_type), body, node.arg())?;

            node.set(Node::new(
                parsed.loc,
                NodeKind::FunctionDeclaration {
                    locals: sub_ctx.locals,
                },
                type_,
            ));
            node.validate();
        }
        ParsedNodeKind::BitCast { ref value } => {
            if let Some(casting_to) = wanted_type {
                let casting_from = type_ast(ctx, None, value, node.arg())?;

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
        ParsedNodeKind::FunctionCall {
            ref calling,
            args: ref parsed_args,
        } => {
            let ptr = type_ast(ctx, None, calling, node.arg())?;
            if let TypeKind::Function {
                args,
                returns,
                is_extern,
            } = ptr.kind()
            {
                if args.len() != parsed_args.len() {
                    ctx.errors.error(calling.loc, format!("Function is of type '{}', which has {} arguments, but {} arguments were given in the call", ptr, args.len(), parsed_args.len()));
                    return Err(());
                }

                for (&wanted, got) in args.iter().zip(parsed_args) {
                    type_ast(ctx, Some(wanted), got, node.arg())?;
                }

                type_ = *returns;
                node.set(Node::new(
                    calling.loc,
                    NodeKind::FunctionCall {
                        is_extern: *is_extern,
                    },
                    type_,
                ));
                node.validate();
            } else {
                ctx.errors.error(
                    calling.loc,
                    format!(
                        "Can only call function on function pointer, found type '{}'",
                        ptr
                    ),
                );
                return Err(());
            }
        }
        ParsedNodeKind::Extern {
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
        ParsedNodeKind::Literal(Literal::Int(num)) => match wanted_type.map(Type::kind) {
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
        ParsedNodeKind::TypeBound {
            ref value,
            ref bound,
        } => {
            if wanted_type.is_some() {
                ctx.errors.warning(
                    parsed.loc,
                    "Unnecessary type bound, the type is already known".to_string(),
                );
            }

            type_ = const_fold_type_expr(ctx, bound)?;
            type_ast(ctx, Some(type_), value, node)?;
        }
        ParsedNodeKind::Binary {
            op,
            ref left,
            ref right,
        } => {
            let left_hand_side = wanted_type.and_then(|t| op.left_hand_side_from_return(t));

            let left_type = type_ast(ctx, left_hand_side, left, node.arg())?;
            let right_type = type_ast(
                ctx,
                op.right_hand_side_from_left(left_type),
                right,
                node.arg(),
            )?;

            type_ = match op.return_from_args(left_type, right_type) {
                Some(type_) => type_,
                None => {
                    ctx.errors.error(
                        parsed.loc,
                        format!(
                            "{:?} doesn't support argument types '{}' and '{}'",
                            op, left_type, right_type
                        ),
                    );
                    return Err(());
                }
            };

            node.set(Node::new(parsed.loc, NodeKind::Binary(op), type_));
            node.validate();
        }
        ParsedNodeKind::Unary { op, ref operand } => {
            // FIXME: We want to specify the wanted type more precisely, but it may
            // depend on the operator. Maybe we want to make referencing and dereferencing
            // their own ast nodes, and not have them be unary operators at all, because they
            // are exceptions from the rule that operators return their own type, so they need
            // special treatment. It might be nice to push this complexity out where there is
            // already such difference in behaviour between nodes.
            match op {
                UnaryOp::AutoCast => {
                    if let Some(wanted_type) = wanted_type {
                        let internal_type = type_ast(ctx, None, operand, node.arg())?;

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

                    let operand = type_ast(ctx, wanted_inner, operand, node.arg())?;
                    type_ = Type::new(TypeKind::Reference(operand));

                    node.set(Node::new(parsed.loc, NodeKind::Unary(op), type_));
                    node.validate();
                }
                UnaryOp::Dereference => {
                    let wanted_inner = wanted_type.map(|v| Type::new(TypeKind::Reference(v)));

                    let operand = type_ast(ctx, wanted_inner, operand, node.arg())?;
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
                    type_ = type_ast(ctx, wanted_type, operand, node.arg())?;

                    node.set(Node::new(parsed.loc, NodeKind::Unary(op), type_));
                    node.validate();
                }
            }
        }
        ParsedNodeKind::Empty => {
            type_ = TypeKind::Empty.into();
            node.set(Node::new(
                parsed.loc,
                NodeKind::Constant(ConstantRef::dangling()),
                type_,
            ));
            node.validate();
        }
        ParsedNodeKind::Break {
            label,
            num_defer_deduplications,
            ref value,
        } => {
            let label_type = ctx.locals.get_label_mut(label).type_;
            let inner_type = type_ast(ctx, label_type, value, node.arg())?;

            ctx.locals.get_label_mut(label).type_ = Some(inner_type);

            // FIXME: This should eventually be the never type since the code never reaches here.
            type_ = Type::new(TypeKind::Empty);

            node.set(Node::new(
                parsed.loc,
                NodeKind::Break(label, num_defer_deduplications),
                type_,
            ));
            node.validate();
        }
        ParsedNodeKind::Block {
            label,
            ref contents,
        } => {
            if let Some(label) = label {
                let label = ctx.locals.get_label_mut(label);
                label.type_ = wanted_type;
            }

            for content in contents.iter().take(contents.len() - 1) {
                type_ast(ctx, None, content, node.arg())?;
            }

            type_ = type_ast(ctx, wanted_type, contents.last().unwrap(), node.arg())?;

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

            node.set(Node::new(parsed.loc, NodeKind::Block { label }, type_));
            node.validate();
        }
        ParsedNodeKind::Member { ref of, name } => {
            let member_of = type_ast(ctx, None, of, node.arg())?;

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
        ParsedNodeKind::Global(name) => {
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
        ParsedNodeKind::Local(local) => {
            type_ = ctx.locals.get(local).type_.unwrap();
            node.set(Node::new(parsed.loc, NodeKind::Local(local), type_));
        }
        ParsedNodeKind::Declare { local, ref value } => {
            let local_type = type_ast(ctx, None, value, node.arg())?;

            ctx.locals.get_mut(local).type_ = Some(local_type);
            type_ = Type::new(TypeKind::Empty);
            node.set(Node::new(parsed.loc, NodeKind::Declare(local), type_));
            node.validate();
        }
        ParsedNodeKind::TypeAsValue(ref inner) => {
            let inner_type = const_fold_type_expr(ctx, inner)?;
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
        ParsedNodeKind::LiteralType(_)
        | ParsedNodeKind::ArrayType(_, _)
        | ParsedNodeKind::StructType { .. }
        | ParsedNodeKind::FunctionType { .. }
        | ParsedNodeKind::BufferType(_)
        | ParsedNodeKind::ReferenceType(_) => {
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

fn const_fold_type_expr<'a>(ctx: &mut Context<'a>, parsed: &'a ParsedNode) -> Result<Type, ()> {
    match parsed.kind {
        ParsedNodeKind::Global(name) => {
            let id = ctx.program.get_member_id(name).unwrap();
            let ptr = ctx.program.get_value_of_member(id).as_ptr();
            Ok(unsafe { *ptr.cast::<Type>() })
        }
        ParsedNodeKind::LiteralType(type_) => Ok(type_),
        ParsedNodeKind::StructType {
            fields: ref parsed_fields,
        } => {
            let mut fields = Vec::with_capacity(parsed_fields.len());
            for &(name, ref parsed_field_type) in parsed_fields {
                let field_type = const_fold_type_expr(ctx, parsed_field_type)?;
                fields.push((name, field_type));
            }
            Ok(Type::new(TypeKind::Struct(fields)))
        }
        ParsedNodeKind::BufferType(ref internal) => {
            let pointee = const_fold_type_expr(ctx, internal)?;
            Ok(TypeKind::Buffer(pointee).into())
        }
        ParsedNodeKind::ArrayType(length, ref internal) => {
            let member = const_fold_type_expr(ctx, internal)?;
            Ok(TypeKind::Array(member, length).into())
        }
        ParsedNodeKind::ReferenceType(ref internal) => {
            let pointee = const_fold_type_expr(ctx, internal)?;
            Ok(TypeKind::Reference(pointee).into())
        }
        ParsedNodeKind::FunctionType {
            is_extern,
            ref args,
            ref returns,
        } => {
            let mut arg_types = Vec::with_capacity(args.len());
            for arg in args {
                arg_types.push(const_fold_type_expr(ctx, arg)?);
            }

            let returns = const_fold_type_expr(ctx, returns)?;

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
fn auto_cast<'a>(
    ctx: &mut Context<'a>,
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
