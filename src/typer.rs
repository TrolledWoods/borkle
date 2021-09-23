use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::locals::LocalVariables;
use crate::location::Location;
use crate::operators::{UnaryOp, BinaryOp};
use crate::parser::{ast::Node as ParsedNode, ast::NodeKind as ParsedNodeKind, Ast as ParsedAst, ast::NodeId as ParsedNodeId};
use crate::program::constant::ConstantRef;
use crate::program::{MemberId, MemberMetaData, PolyOrMember, Program, Task};
use crate::self_buffer::{SelfBox, SelfBuffer, SelfTree};
use crate::thread_pool::ThreadContext;
use crate::types::{Alias, IntTypeKind, PtrPermits, Type, TypeData, TypeKind};
pub use ast::{Node, NodeKind};
use infer::WantedType;
use std::sync::Arc;
use ustr::Ustr;

pub type Ast = SelfTree<Node>;

pub mod ast;
mod infer;

struct Context<'a, 'b> {
    is_const: bool,
    thread_context: &'a mut ThreadContext<'b>,
    errors: &'a mut ErrorCtx,
    program: &'b Program,
    locals: LocalVariables,
    deps: &'a mut DependencyList,
    poly_args: &'a [(Type, ConstantRef)],
    ast: &'a ParsedAst,
}

pub fn process_ast<'a>(
    errors: &mut ErrorCtx,
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    locals: LocalVariables,
    parsed: &ParsedAst,
    wanted_type: Option<Type>,
    poly_args: &[(Type, ConstantRef)],
) -> Result<(DependencyList, LocalVariables, Ast), ()> {
    profile::profile!("Type ast");

    let mut deps = DependencyList::new();
    let mut ctx = Context {
        is_const: false,
        thread_context,
        errors,
        program,
        locals,
        deps: &mut deps,
        poly_args,
        ast: parsed,
    };
    let mut buffer = SelfBuffer::new();
    let root = type_ast(&mut ctx, wanted_type.into(), parsed.root, &mut buffer)?;
    let tree = buffer.insert_root(root);
    let locals = ctx.locals;
    Ok((deps, locals, tree))
}

/// If the `wanted_type` is Some(type_), this function itself will generate an error if the types
/// do not match, i.e., if Some(type_) is passed as the `wanted_type`, if the function returns Ok
/// that is guaranteed to be the type_ passed in.
fn type_ast<'a>(
    ctx: &mut Context<'a, '_>,
    wanted_type: WantedType,
    parsed: ParsedNodeId,
    buffer: &mut SelfBuffer,
) -> Result<Node, ()> {
    let node = match ctx.ast.get(parsed).kind {
        ParsedNodeKind::PolymorphicArgument(index) => {
            let (type_, constant_ref) = ctx.poly_args[index];
            Node::new(ctx.ast.get(parsed).loc, NodeKind::Constant(constant_ref, None), type_)
        }
        ParsedNodeKind::Parenthesis(inner) => type_ast(ctx, wanted_type, inner, buffer)?,
        ParsedNodeKind::BuiltinFunction(kind) => {
            let specific = wanted_type.get_specific().ok_or_else(|| ctx.errors.error(ctx.ast.get(parsed).loc, "A builtin function definition needs a type bound to work(why are you even messing with these, these are supposed to be defined withing the standard librarys 'intrinsics.bo' file! XD p.s: giving a bad type definition could segfault the compiler right now)".to_string()))?;

            let id = ctx.program.insert_defined_function(
                ctx.ast.get(parsed).loc,
                Vec::new(),
                crate::ir::Routine::Builtin(kind),
            );

            if let TypeKind::Function { args, returns } = specific.kind() {
                // FIXME: This is duplicated in emit, could there be a nice way to deduplicate them?
                if ctx.program.arguments.release {
                    crate::c_backend::function_declaration(
                        &mut ctx.thread_context.c_headers,
                        crate::c_backend::c_format_function(id),
                        args,
                        *returns,
                    );

                    ctx.thread_context.c_headers.push_str(";\n");

                    crate::c_backend::function_declaration(
                        &mut ctx.thread_context.c_declarations,
                        crate::c_backend::c_format_function(id),
                        args,
                        *returns,
                    );
                    ctx.thread_context.c_declarations.push_str(" {\n");

                    let routine = ctx.program.get_routine(id).unwrap();
                    crate::c_backend::routine_to_c(
                        &mut ctx.thread_context.c_declarations,
                        &routine,
                        args,
                        *returns,
                    );
                    ctx.thread_context.c_declarations.push_str("}\n");
                }

                Node::new(
                    ctx.ast.get(parsed).loc,
                    NodeKind::Constant(
                        ctx.program
                            .insert_buffer(specific, &id as *const _ as *const u8),
                        None,
                    ),
                    specific,
                )
            } else {
                ctx.errors.error(
                    ctx.ast.get(parsed).loc,
                    "The type of a built in function has to be a function".to_string(),
                );
                return Err(());
            }
        }
        ParsedNodeKind::ConstAtEvaluation {
            ref locals,
            inner,
        } => {
            let mut locals = std::mem::replace(&mut ctx.locals, locals.clone());

            let old_const = ctx.is_const;
            ctx.is_const = true;
            let inner = type_ast(ctx, wanted_type, inner, buffer)?;
            ctx.is_const = old_const;

            if !inner.type_().can_be_stored_in_constant() {
                ctx.errors.error(ctx.ast.get(parsed).loc, format!("'{}' cannot be stored in a constant, because it contains types that the compiler cannot reason about properly, such as '&any', '&void', '[] void', or similar", inner.type_()));
                return Err(());
            }

            locals = std::mem::replace(&mut ctx.locals, locals);

            if let NodeKind::Constant(_, _)
            | NodeKind::Global(_, _)
            | NodeKind::ConstAtEvaluation { .. } = inner.kind()
            {
                ctx.errors.warning(
                    ctx.ast.get(parsed).loc,
                    "Unnecessary 'const', the expression is already constant".to_string(),
                );
            }

            let type_ = inner.type_();
            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::ConstAtEvaluation {
                    locals,
                    inner: buffer.insert(inner),
                },
                type_,
            )
        }
        ParsedNodeKind::ConstAtTyping {
            ref locals,
            inner,
        } => {
            let mut locals = std::mem::replace(&mut ctx.locals, locals.clone());
            let inner = type_ast(ctx, wanted_type, inner, buffer)?;

            if !inner.type_().can_be_stored_in_constant() {
                ctx.errors.error(ctx.ast.get(parsed).loc, format!("'{}' cannot be stored in a constant, because it contains types that the compiler cannot reason about properly, such as '&any', '&void', '[] void', or similar", inner.type_()));
                return Err(());
            }

            locals = std::mem::replace(&mut ctx.locals, locals);

            if let NodeKind::Constant(_, _) = inner.kind() {
                ctx.errors.warning(
                    ctx.ast.get(parsed).loc,
                    "Unnecessary 'const', the expression is already constant".to_string(),
                );
            }

            let constant =
                crate::interp::emit_and_run(ctx.thread_context, ctx.program, locals, &inner);

            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::Constant(constant, None),
                inner.type_(),
            )
        }
        ParsedNodeKind::Defer { deferring } => {
            let typed = type_ast(ctx, WantedType::none(), deferring, buffer)?;

            if let NodeKind::Constant(_, _) | NodeKind::ConstAtEvaluation { .. } = typed.kind() {
                ctx.errors.warning(ctx.ast.get(parsed).loc, "Useless defer".to_string());
            }

            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::Defer {
                    deferred: buffer.insert(typed),
                },
                Type::new(TypeKind::Empty),
            )
        }
        ParsedNodeKind::Literal(Literal::Float(num)) => {
            match wanted_type.get_specific().map(Type::kind) {
                Some(TypeKind::F32) | None => {
                    // FIXME: Maybe we want a compiler error for when num is truncated?
                    #[allow(clippy::cast_possible_truncation)]
                    let bytes = (num as f32).to_bits().to_le_bytes();
                    let type_ = Type::new(TypeKind::F32);

                    Node::new(
                        ctx.ast.get(parsed).loc,
                        NodeKind::Constant(ctx.program.insert_buffer(type_, bytes.as_ptr()), None),
                        type_,
                    )
                }
                Some(TypeKind::F64) => {
                    let bytes = num.to_bits().to_le_bytes();
                    let type_ = Type::new(TypeKind::F64);

                    Node::new(
                        ctx.ast.get(parsed).loc,
                        NodeKind::Constant(ctx.program.insert_buffer(type_, bytes.as_ptr()), None),
                        type_,
                    )
                }
                Some(wanted_type) => {
                    ctx.errors.error(
                        ctx.ast.get(parsed).loc,
                        format!("Expected '{}', found float", wanted_type),
                    );
                    return Err(());
                }
            }
        }
        ParsedNodeKind::Literal(Literal::String(ref data)) => {
            let u8_type = Type::new(TypeKind::Int(IntTypeKind::U8));

            if let Some(TypeKind::Int(IntTypeKind::U8)) = wanted_type.get_specific().map(Type::kind)
            {
                let bytes = data.as_bytes();

                if bytes.len() != 1 {
                    ctx.errors.error(
                        ctx.ast.get(parsed).loc,
                        "String literal is supposed to be a 'u8', but it's length is not 1"
                            .to_string(),
                    );
                    return Err(());
                }

                let ptr = ctx.program.insert_buffer(u8_type, bytes.as_ptr());
                Node::new(ctx.ast.get(parsed).loc, NodeKind::Constant(ptr, None), u8_type)
            } else {
                let type_ = Type::new(TypeKind::Buffer(u8_type));
                let ptr = ctx.program.insert_buffer(
                    type_,
                    &crate::types::BufferRepr {
                        ptr: data.as_ptr() as *mut _,
                        length: data.len(),
                    } as *const _ as *const _,
                );
                Node::new(ctx.ast.get(parsed).loc, NodeKind::Constant(ptr, None), type_)
            }
        }
        ParsedNodeKind::ArrayLiteral(ref parsed_elements) => {
            let mut element_type = wanted_type.get_element().ok_or_else(|| {
                ctx.errors.error(
                    ctx.ast.get(parsed).loc,
                    format!("Expected '{}', found array literal", wanted_type),
                )
            })?;

            let mut elements = Vec::with_capacity(parsed_elements.len());
            for &parsed_element in parsed_elements {
                let element = type_ast(ctx, element_type, parsed_element, buffer)?;
                element_type = WantedType::specific(None, element.type_());
                elements.push(buffer.insert(element));
            }

            let inner = element_type.get_specific().ok_or_else(||
                    ctx.errors.error(ctx.ast.get(parsed).loc, "Because this is an empty array, the types of the elements cannot be inferred; you have to specify a type bound".to_string())
            )?;
            let type_ = Type::new(TypeKind::Array(inner, elements.len()));

            Node::new(ctx.ast.get(parsed).loc, NodeKind::ArrayLiteral { elements }, type_)
        }
        ParsedNodeKind::For {
            iterator,
            iteration_var,
            iterating,
            body,
            label,
            else_body,
        } => {
            ctx.locals.get_label_mut(label).type_ = wanted_type.get_specific();
            ctx.locals.get_mut(iteration_var).type_ =
                Some(Type::new(TypeKind::Int(IntTypeKind::Usize)));

            let mut iterating = type_ast(ctx, WantedType::none(), iterating, buffer)?;

            let iterator_type = match iterating.type_().kind() {
                TypeKind::Range(inner)
                    if matches!(inner.kind(), TypeKind::Int(_) | TypeKind::Reference { .. }) =>
                {
                    *inner
                }
                TypeKind::Buffer(inner) => Type::new(TypeKind::Reference {
                    pointee: *inner,
                    permits: PtrPermits::READ_WRITE,
                }),
                TypeKind::Reference { pointee, permits } => match pointee.kind() {
                    TypeKind::Array(inner, length) => {
                        iterating = Node::new(
                            ctx.ast.get(parsed).loc,
                            NodeKind::ArrayToBuffer {
                                length: *length,
                                array: buffer.insert(iterating),
                            },
                            Type::new(TypeKind::Buffer(*inner)),
                        );
                        Type::new(TypeKind::Reference {
                            pointee: *inner,
                            permits: *permits,
                        })
                    }
                    _ => {
                        ctx.errors.error(
                            iterating.loc,
                            format!(
                                "'{}' cannot be iterated over in a for loop",
                                iterating.type_()
                            ),
                        );
                        return Err(());
                    }
                },
                _ => {
                    ctx.errors.error(
                        iterating.loc,
                        format!(
                            "'{}' cannot be iterated over in a for loop",
                            iterating.type_()
                        ),
                    );
                    return Err(());
                }
            };

            ctx.locals.get_mut(iterator).type_ = Some(iterator_type);
            let body = type_ast(ctx, WantedType::none(), body, buffer)?;

            let else_body = if let Some(else_body) = else_body {
                let else_body = type_ast(ctx, wanted_type, else_body, buffer)?;
                Some(buffer.insert(else_body))
            } else {
                None
            };

            let type_ = else_body
                .as_ref()
                .map_or(Type::new(TypeKind::Empty), |node| node.type_());

            let label_def = ctx.locals.get_label(label);
            if let Some(label_type) = label_def.type_ {
                if label_type != type_ {
                    ctx.errors.error(
                        label_def.first_break_location.unwrap(),
                        format!("Expected '{}', found '{}'", type_, label_type),
                    );
                    return Err(());
                }
            }

            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::For {
                    iterator,
                    iteration_var,
                    iterating: buffer.insert(iterating),
                    body: buffer.insert(body),
                    label,
                    else_body,
                },
                type_,
            )
        }
        ParsedNodeKind::While {
            condition,
            body,
            else_body,
            iteration_var,
            label,
        } => {
            ctx.locals.get_label_mut(label).type_ = wanted_type.get_specific();
            ctx.locals.get_mut(iteration_var).type_ =
                Some(Type::new(TypeKind::Int(IntTypeKind::Usize)));

            let condition = type_ast(
                ctx,
                WantedType::specific(None, Type::new(TypeKind::Bool)),
                condition,
                buffer,
            )?;
            let body = type_ast(ctx, WantedType::none(), body, buffer)?;

            let else_body = if let Some(else_body) = else_body {
                let else_body = type_ast(ctx, wanted_type, else_body, buffer)?;
                Some(buffer.insert(else_body))
            } else {
                None
            };

            let type_ = else_body
                .as_ref()
                .map_or(Type::new(TypeKind::Empty), |node| node.type_());

            let label_def = ctx.locals.get_label(label);
            if let Some(label_type) = label_def.type_ {
                if label_type != type_ {
                    ctx.errors.error(
                        label_def.first_break_location.unwrap(),
                        format!("Expected '{}', found '{}'", type_, label_type),
                    );
                    return Err(());
                }
            }

            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::While {
                    condition: buffer.insert(condition),
                    iteration_var,
                    body: buffer.insert(body),
                    else_body,
                    label,
                },
                type_,
            )
        }
        ParsedNodeKind::If {
            condition,
            true_body,
            false_body: None,
        } => {
            let condition = type_ast(
                ctx,
                WantedType::specific(None, Type::new(TypeKind::Bool)),
                condition,
                buffer,
            )?;
            let true_body = type_ast(ctx, WantedType::none(), true_body, buffer)?;

            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::If {
                    condition: buffer.insert(condition),
                    true_body: buffer.insert(true_body),
                    false_body: None,
                },
                Type::new(TypeKind::Empty),
            )
        }
        ParsedNodeKind::If {
            condition,
            true_body,
            false_body: Some(false_body),
        } => {
            let condition = type_ast(
                ctx,
                WantedType::specific(None, Type::new(TypeKind::Bool)),
                condition,
                buffer,
            )?;

            let true_body = type_ast(ctx, wanted_type, true_body, buffer)?;
            let false_body = type_ast(
                ctx,
                WantedType::specific(wanted_type.loc, true_body.type_()),
                false_body,
                buffer,
            )?;

            if false_body.type_() != true_body.type_() {
                ctx.errors.error(
                    ctx.ast.get(parsed).loc,
                    format!("Both the if and the else body have to return the same type. The if body has type '{}' while the else body has type '{}'", true_body.type_(), false_body.type_()),
                );
                return Err(());
            }

            let type_ = true_body.type_();

            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::If {
                    condition: buffer.insert(condition),
                    true_body: buffer.insert(true_body),
                    false_body: Some(buffer.insert(false_body)),
                },
                type_,
            )
        }
        ParsedNodeKind::Binary {
            op: BinaryOp::Assign,
            left: lvalue,
            right: rvalue,
        } => {
            let lvalue = type_ast(ctx, WantedType::none(), lvalue, buffer)?;
            make_sure_valid_lvalue(ctx, &lvalue, PtrPermits::WRITE)?;
            let rvalue = type_ast(
                ctx,
                WantedType::specific(Some(lvalue.loc), lvalue.type_()),
                rvalue,
                buffer,
            )?;

            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::Assign {
                    lvalue: buffer.insert(lvalue),
                    rvalue: buffer.insert(rvalue),
                },
                Type::new(TypeKind::Empty),
            )
        }
        ParsedNodeKind::Zeroed => {
            let wanted = wanted_type.get_specific().ok_or_else(|| {
                ctx.errors.error(
                    ctx.ast.get(parsed).loc,
                    "Type has to be known at this point; put a type bound on this!".to_string(),
                )
            })?;

            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::Constant(ctx.program.insert_zeroed_buffer(wanted), None),
                wanted,
            )
        }
        ParsedNodeKind::Uninit => {
            let wanted_type = wanted_type.get_specific().ok_or_else(|| {
                ctx.errors.error(
                    ctx.ast.get(parsed).loc,
                    "Type has to be known at this point; put a type bound on this!".to_string(),
                )
            })?;
            Node::new(ctx.ast.get(parsed).loc, NodeKind::Uninit, wanted_type)
        }
        ParsedNodeKind::FunctionDeclaration {
            ref locals,
            ref args,
            ref default_args,
            returns,
            ref body,
            ref body_deps,
        } => {
            let mut locals = locals.clone();

            let mut arg_types = Vec::with_capacity(args.len() + default_args.len());
            let mut arg_names = Vec::with_capacity(args.len() + default_args.len());

            for (local, &(name, node)) in locals.iter_mut().zip(args) {
                let arg_type = const_fold_type_expr(ctx, node, buffer)?;
                local.type_ = Some(arg_type);
                arg_types.push(arg_type);
                arg_names.push(name);
            }

            let mut default_values = Vec::with_capacity(default_args.len());
            for (local, &(name, node)) in locals.iter_mut().skip(args.len()).zip(default_args) {
                let arg_value = type_ast(ctx, WantedType::none(), node, buffer)?;

                if let NodeKind::Constant(constant, _) = *arg_value.kind() {
                    default_values.push(constant);
                } else {
                    ctx.errors
                        .error(ctx.ast.get(node).loc, "Expected constant expression".to_string());
                    return Err(());
                }

                local.type_ = Some(arg_value.type_());
                arg_types.push(arg_value.type_());
                arg_names.push(name);
            }

            let return_type = const_fold_type_expr(ctx, returns, buffer)?;

            let type_ = Type::new(TypeKind::Function {
                args: arg_types,
                returns: return_type,
            });

            let function_id = ctx.program.insert_function(ctx.ast.get(parsed).loc);
            ctx.program.queue_task(
                body_deps.clone(),
                Task::TypeFunction(
                    function_id,
                    locals,
                    Arc::clone(&body),
                    return_type,
                    type_,
                    ctx.poly_args.to_vec(),
                ),
            );

            let function_id_buffer = ctx
                .program
                .insert_buffer(type_, &function_id as *const _ as *const u8);

            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::Constant(
                    function_id_buffer,
                    Some(Arc::new(MemberMetaData::Function {
                        arg_names,
                        default_values,
                    })),
                ),
                type_,
            )
        }
        ParsedNodeKind::BitCast { value } => {
            let casting_to = wanted_type.get_specific().ok_or_else(|| {
                ctx.errors.error(ctx.ast.get(parsed).loc, "Can only cast if the type we cast to is known; add a type bound after the cast to tell it what to cast to".to_string())
            })?;
            let casting_from = type_ast(ctx, WantedType::none(), value, buffer)?;

            if casting_from.type_().size() != casting_to.size() {
                ctx.errors.error(ctx.ast.get(parsed).loc, format!("Cannot bit_cast from '{}' to '{}', the sizes of the types have to be the same.", casting_from.type_(), casting_to));
                return Err(());
            }

            if casting_from.type_() == casting_to {
                ctx.errors.warning(
                    ctx.ast.get(parsed).loc,
                    "Unnecessary bit_cast, the types are the same".to_string(),
                );
            }

            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::BitCast {
                    value: buffer.insert(casting_from),
                },
                casting_to,
            )
        }
        ParsedNodeKind::FunctionCall {
            calling,
            args: ref parsed_args,
            ref named_args,
        } => {
            let calling = type_ast(ctx, WantedType::none(), calling, buffer)?;
            if let Some((arg_types, returns)) = calling.type_().call_scheme() {
                if parsed_args.len() > arg_types.len() {
                    ctx.errors.error(
                        calling.loc,
                        format!("Too many arguments passed, expected {}", arg_types.len()),
                    );
                    return Err(());
                }

                let mut args = Vec::with_capacity(arg_types.len());
                for (i, &got) in parsed_args.iter().enumerate() {
                    let arg = type_ast(ctx, WantedType::specific(None, arg_types[i]), got, buffer)?;
                    args.push((i, buffer.insert(arg)));
                }

                if let NodeKind::Global(_, meta_data) = calling.kind() {
                    if let MemberMetaData::Function {
                        arg_names,
                        default_values,
                    } = &**meta_data
                    {
                        for &(ref name, arg) in named_args {
                            if let Some(i) = arg_names.iter().position(|arg_name| arg_name == name)
                            {
                                if args.iter().any(|&(arg_i, _)| arg_i == i) {
                                    ctx.errors.error(
                                        ctx.ast.get(arg).loc,
                                        format!("Argument '{}' already defined", name),
                                    );
                                    return Err(());
                                }

                                let arg = type_ast(
                                    ctx,
                                    WantedType::specific(None, arg_types[i]),
                                    arg,
                                    buffer,
                                )?;
                                args.push((i, buffer.insert(arg)));
                            } else {
                                ctx.errors.error(
                                        ctx.ast.get(arg).loc,
                                        format!("Argument '{}' does not exist, available arguments are: {:?}", name, arg_names),
                                    );
                                return Err(());
                            }
                        }

                        // Go through all the default arguments, and try to fill in the gaps left
                        // by the caller.
                        let num_non_default_args = arg_types.len() - default_values.len();
                        for (i, default_value) in default_values
                            .iter()
                            .enumerate()
                            .map(|(i, val)| (i + num_non_default_args, val))
                        {
                            if !args.iter().any(|&(arg_i, _)| arg_i == i) {
                                args.push((
                                    i,
                                    buffer.insert(Node::new(
                                        calling.loc,
                                        NodeKind::Constant(*default_value, None),
                                        arg_types[i],
                                    )),
                                ));
                            }
                        }
                    } else if !named_args.is_empty() {
                        ctx.errors.error(
                            calling.loc,
                            "This function has no named parameters".to_string(),
                        );
                        return Err(());
                    }
                } else if !named_args.is_empty() {
                    ctx.errors.error(calling.loc, "Only functions declared in constants can be called with named arguments, not function pointers".to_string());
                    return Err(());
                }

                if arg_types.len() != args.len() {
                    ctx.errors.error(calling.loc, format!("Function is of type '{}', which has {} arguments, but {} arguments were given in the call", calling.type_(), arg_types.len(), parsed_args.len()));
                    return Err(());
                }

                let calling_loc = calling.loc;
                let node = Node::new(
                    calling.loc,
                    NodeKind::FunctionCall {
                        calling: buffer.insert(calling),
                        args,
                    },
                    *returns,
                );

                if let Some(specific) = wanted_type.get_specific() {
                    if specific != *returns {
                        auto_cast(ctx, calling_loc, node, specific, buffer)?
                    } else {
                        node
                    }
                } else {
                    node
                }
            } else {
                ctx.errors.error(
                    calling.loc,
                    format!(
                        "Can only call function on function pointer, found type '{}'",
                        calling.type_(),
                    ),
                );
                return Err(());
            }
        }
        ParsedNodeKind::Literal(Literal::Int(num)) => {
            const DEFAULT_KIND: &TypeKind = &TypeKind::Int(IntTypeKind::I32);

            let wanted_type_kind = wanted_type.get_specific().map_or(DEFAULT_KIND, Type::kind);

            match wanted_type_kind {
                TypeKind::Int(int) => {
                    let bytes = num.to_le_bytes();

                    if !int.range().contains(&(num as i128)) {
                        let range = int.range();
                        ctx.errors.error(
                            ctx.ast.get(parsed).loc,
                            format!("Given integer does not fit within a '{:?}', only values from {} to {} fit in this integer", int, range.start(), range.end())
                        );
                        return Err(());
                    }

                    let type_ = (*int).into();
                    Node::new(
                        ctx.ast.get(parsed).loc,
                        NodeKind::Constant(ctx.program.insert_buffer(type_, bytes.as_ptr()), None),
                        type_,
                    )
                }
                _ => {
                    if let Some(loc) = wanted_type.loc {
                        ctx.errors.info(loc, format!("This is '{}'", wanted_type));
                    }

                    ctx.errors.error(
                        ctx.ast.get(parsed).loc,
                        format!("Expected '{}', found integer", wanted_type),
                    );
                    return Err(());
                }
            }
        }
        ParsedNodeKind::TypeBound {
            value,
            bound,
        } => {
            if wanted_type.get_specific().is_some() {
                ctx.errors.warning(
                    ctx.ast.get(parsed).loc,
                    "Unnecessary type bound, the type is already known".to_string(),
                );
            }

            let bound_loc = ctx.ast.get(bound).loc;
            let bound = const_fold_type_expr(ctx, bound, buffer)?;
            type_ast(
                ctx,
                WantedType::specific(Some(bound_loc), bound),
                value,
                buffer,
            )?
        }
        ParsedNodeKind::Binary {
            op,
            left,
            right,
        } => {
            let left_hand_side = wanted_type
                .get_specific()
                .and_then(|t| op.left_hand_side_from_return(t));

            let left = type_ast(ctx, left_hand_side.into(), left, buffer)?;
            let right = type_ast(
                ctx,
                op.right_hand_side_from_left(left.type_()).into(),
                right,
                buffer,
            )?;

            let type_ = match op.return_from_args(left.type_(), right.type_()) {
                Some(type_) => type_,
                None => {
                    ctx.errors.error(
                        ctx.ast.get(parsed).loc,
                        format!(
                            "{:?} doesn't support argument types '{}' and '{}'",
                            op,
                            left.type_(),
                            right.type_()
                        ),
                    );
                    return Err(());
                }
            };

            if let (NodeKind::Constant(left_val, _), NodeKind::Constant(right_val, _)) =
                (left.kind(), right.kind())
            {
                let constant_ref = ctx
                    .program
                    .insert_buffer_from_operation(type_, |out| unsafe {
                        op.run(
                            left.type_(),
                            right.type_(),
                            left_val.as_ptr(),
                            right_val.as_ptr(),
                            out,
                        )
                    });
                Node::new(ctx.ast.get(parsed).loc, NodeKind::Constant(constant_ref, None), type_)
            } else {
                Node::new(
                    ctx.ast.get(parsed).loc,
                    NodeKind::Binary {
                        op,
                        left: buffer.insert(left),
                        right: buffer.insert(right),
                    },
                    type_,
                )
            }
        }
        ParsedNodeKind::Unary { op, operand } => {
            // FIXME: We want to specify the wanted type more precisely, but it may
            // depend on the operator. Maybe we want to make referencing and dereferencing
            // their own ast nodes, and not have them be unary operators at all, because they
            // are exceptions from the rule that operators return their own type, so they need
            // special treatment. It might be nice to push this complexity out where there is
            // already such difference in behaviour between nodes.
            match op {
                UnaryOp::AutoCast => {
                    let wanted_type = wanted_type.get_specific().ok_or_else(|| {
                        ctx.errors.error(ctx.ast.get(parsed).loc, "Casting can only be done if the type is known; are you sure you want to cast here?".to_string())
                    })?;
                    let internal = type_ast(ctx, WantedType::none(), operand, buffer)?;
                    auto_cast(ctx, ctx.ast.get(parsed).loc, internal, wanted_type, buffer)?
                }
                UnaryOp::Dereference => {
                    // @Cleanup: We probably want to add some permits to this pointer at some
                    // point... but right now we don't know enough to calculate that
                    let wanted_inner = wanted_type.get_specific().map(|v| {
                        Type::new(TypeKind::Reference {
                            pointee: v,
                            permits: PtrPermits::READ_WRITE,
                        })
                    });

                    let operand = type_ast(ctx, wanted_inner.into(), operand, buffer)?;
                    let type_ = if let TypeKind::Reference { pointee, .. } = *operand.type_().kind()
                    {
                        pointee
                    } else {
                        ctx.errors.error(
                            ctx.ast.get(parsed).loc,
                            format!(
                                "Cannot dereference '{}', because it's not a refernece",
                                operand.type_()
                            ),
                        );
                        return Err(());
                    };

                    if let NodeKind::Constant(constant, _) = operand.kind() {
                        let constant = ctx.program.insert_buffer(type_, unsafe {
                            *constant.as_ptr().cast::<*const u8>()
                        });
                        Node::new(ctx.ast.get(parsed).loc, NodeKind::Constant(constant, None), type_)
                    } else {
                        Node::new(
                            ctx.ast.get(parsed).loc,
                            NodeKind::Unary {
                                op,
                                operand: buffer.insert(operand),
                            },
                            type_,
                        )
                    }
                }
                _ => {
                    let operand = type_ast(ctx, wanted_type, operand, buffer)?;
                    let type_ = operand.type_();

                    Node::new(
                        ctx.ast.get(parsed).loc,
                        NodeKind::Unary {
                            op,
                            operand: buffer.insert(operand),
                        },
                        type_,
                    )
                }
            }
        }
        ParsedNodeKind::Reference(operand, permits) => {
            let wanted_inner = wanted_type.get_pointee().ok_or_else(|| {
                ctx.errors.error(
                    ctx.ast.get(parsed).loc,
                    format!("Expected '{}', got a reference of something", wanted_type),
                )
            })?;

            let operand = type_ast(ctx, wanted_inner, operand, buffer)?;
            make_sure_valid_lvalue(ctx, &operand, permits)?;

            match wanted_type.get_specific() {
                Some(Type(TypeData {
                    kind: TypeKind::Reference { .. },
                    ..
                }))
                | None => {
                    let type_ = Type::new(TypeKind::Reference {
                        pointee: operand.type_(),
                        permits,
                    });

                    if let NodeKind::Constant(constant, _) = operand.kind() {
                        let constant = ctx.program.insert_buffer(
                            type_,
                            &(constant.as_ptr() as usize).to_le_bytes() as *const _ as *const _,
                        );
                        Node::new(ctx.ast.get(parsed).loc, NodeKind::Constant(constant, None), type_)
                    } else {
                        Node::new(
                            ctx.ast.get(parsed).loc,
                            NodeKind::Unary {
                                op: UnaryOp::Reference,
                                operand: buffer.insert(operand),
                            },
                            type_,
                        )
                    }
                }
                Some(wanted) => {
                    let type_ = Type::new(TypeKind::Reference {
                        pointee: operand.type_(),
                        permits: PtrPermits::READ_WRITE,
                    });
                    let from = Node::new(
                        ctx.ast.get(parsed).loc,
                        NodeKind::Unary {
                            op: UnaryOp::Reference,
                            operand: buffer.insert(operand),
                        },
                        type_,
                    );
                    auto_cast(ctx, ctx.ast.get(parsed).loc, from, wanted, buffer)?
                }
            }
        }
        ParsedNodeKind::Empty => Node::new(
            ctx.ast.get(parsed).loc,
            NodeKind::Constant(ConstantRef::dangling(), None),
            Type::new(TypeKind::Empty),
        ),
        ParsedNodeKind::Break {
            label,
            num_defer_deduplications,
            value,
        } => {
            let label_mut = ctx.locals.get_label_mut(label);
            let label_type = label_mut.type_;
            let label_loc = label_mut.first_break_location;
            let value = type_ast(
                ctx,
                WantedType::maybe_specific(label_loc, label_type),
                value,
                buffer,
            )?;

            ctx.locals.get_label_mut(label).type_ = Some(value.type_());

            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::Break {
                    label,
                    num_defer_deduplications,
                    value: buffer.insert(value),
                },
                Type::new(TypeKind::Empty),
            )
        }
        ParsedNodeKind::Block {
            label,
            contents: ref parsed_contents,
        } => {
            if let Some(label) = label {
                let label = ctx.locals.get_label_mut(label);
                label.type_ = wanted_type.get_specific();
            }

            let mut contents = Vec::with_capacity(parsed_contents.len());
            for &parsed_content in parsed_contents.iter().take(parsed_contents.len() - 1) {
                let content = type_ast(ctx, WantedType::none(), parsed_content, buffer)?;

                if let NodeKind::Constant(_, _) | NodeKind::ConstAtEvaluation { .. } =
                    content.kind()
                {
                    ctx.errors.warning(
                        ctx.ast.get(parsed_content).loc,
                        "Useless expression, this is a constant!".to_string(),
                    );
                }

                contents.push(buffer.insert(content));
            }

            let parsed_last = *parsed_contents.last().unwrap();
            let last = type_ast(ctx, wanted_type, parsed_last, buffer)?;

            let type_ = last.type_();
            contents.push(buffer.insert(last));

            if let Some(label) = label {
                let label = ctx.locals.get_label_mut(label);
                if let Some(label_type) = label.type_ {
                    if label_type != type_ {
                        ctx.errors
                            .info(ctx.ast.get(parsed).loc, "Block is defined here".to_string());
                        ctx.errors.info(
                            label.first_break_location.unwrap(),
                            format!("Here you break to the block with the type '{}'", label_type),
                        );
                        ctx.errors.error(
                            ctx.ast.get(parsed_last).loc,
                            format!("Tried returning type '{}' from a block, but you also tried breaking to it with the type '{}'", type_, label_type),
                        );
                        return Err(());
                    }
                } else {
                    label.type_ = Some(type_);
                }
            }

            Node::new(ctx.ast.get(parsed).loc, NodeKind::Block { label, contents }, type_)
        }
        ParsedNodeKind::Member { of, name } => {
            let mut member_of = type_ast(ctx, WantedType::none(), of, buffer)?;

            // Dereference it as many times as necessary
            while let TypeKind::Reference { pointee, .. } = *member_of.type_().kind() {
                member_of = Node::new(
                    ctx.ast.get(parsed).loc,
                    NodeKind::Unary {
                        op: UnaryOp::Dereference,
                        operand: buffer.insert(member_of),
                    },
                    pointee,
                );
            }

            if let Some(member) = member_of.type_().member(name) {
                Node::new(
                    ctx.ast.get(parsed).loc,
                    NodeKind::Member {
                        name,
                        of: buffer.insert(member_of),
                    },
                    member.type_,
                )
            } else {
                ctx.errors.error(
                    ctx.ast.get(parsed).loc,
                    format!(
                        "The type '{}' does not have member '{}'",
                        member_of.type_(),
                        name
                    ),
                );
                return Err(());
            }
        }
        ParsedNodeKind::GlobalForTyping(scope, name, ref poly_args) => {
            let id = ctx.program.get_member_id(scope, name).unwrap();

            let id = monomorphise(
                ctx,
                ctx.ast.get(parsed).loc,
                name,
                id,
                MemberDep::ValueAndCallableIfFunction,
                poly_args,
                buffer,
            )?;

            let (type_, meta_data) = ctx.program.get_member_meta_data(id);
            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::Constant(ctx.program.get_value_of_member(id), Some(meta_data)),
                type_,
            )
        }
        ParsedNodeKind::Global(scope, name, ref poly_args) => {
            let id = ctx.program.get_member_id(scope, name).unwrap();
            let id = monomorphise(
                ctx,
                ctx.ast.get(parsed).loc,
                name,
                id,
                MemberDep::Type,
                poly_args,
                buffer,
            )?;

            if ctx.is_const {
                ctx.deps.add(
                    ctx.ast.get(parsed).loc,
                    DepKind::Member(id, MemberDep::ValueAndCallableIfFunction),
                );
            } else {
                ctx.deps
                    .add(ctx.ast.get(parsed).loc, DepKind::Member(id, MemberDep::Value));
            }

            let (type_, meta_data) = ctx.program.get_member_meta_data(id);
            Node::new(ctx.ast.get(parsed).loc, NodeKind::Global(id, meta_data), type_)
        }
        ParsedNodeKind::Local(local_id) => {
            let local = ctx.locals.get(local_id);
            let local_type = local.type_.unwrap();
            if !wanted_type.type_fits(local_type) {
                ctx.errors
                    .info(local.loc, format!("'{}' declared here", local.name));
            }
            Node::new(ctx.ast.get(parsed).loc, NodeKind::Local(local_id), local_type)
        }
        ParsedNodeKind::Declare {
            local,
            value: parsed_value,
        } => {
            let value = type_ast(ctx, WantedType::none(), parsed_value, buffer)?;

            ctx.locals.get_mut(local).type_ = Some(value.type_());
            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::Declare {
                    local,
                    value: buffer.insert(value),
                },
                Type::new(TypeKind::Empty),
            )
        }
        ParsedNodeKind::TypeAsValue(inner) => {
            let inner_type = const_fold_type_expr(ctx, inner, buffer)?;
            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::Constant(
                    ctx.program.insert_buffer(
                        Type::new(TypeKind::Type),
                        &(inner_type.as_ptr() as usize).to_le_bytes() as *const _,
                    ),
                    None,
                ),
                Type::new(TypeKind::Type),
            )
        }
        ParsedNodeKind::NamedType {
            name,
            ref fields,
            ref aliases,
        } => {
            let mut typed_fields = Vec::with_capacity(fields.len());
            for &(field_name, field_type) in fields {
                let type_ = const_fold_type_expr(ctx, field_type, buffer)?;
                typed_fields.push((field_name, type_));
            }

            let mut resolved_aliases = Vec::with_capacity(aliases.len());
            for &(alias_name, ref path) in aliases {
                let indirections = path.len();

                // Since the first element of the path refers to the current struct,
                // and the current struct is not created yet, we have to manually find
                // that member.
                let (&(first_loc, first), path) =
                    path.split_first().expect("Slice here should not be empty");

                let (mut offset, mut type_) = crate::types::get_struct_field(&typed_fields, first)
                    .ok_or_else(|| {
                        ctx.errors.error(
                            first_loc,
                            format!("Cannot alias '{}', it's not a field", first),
                        )
                    })?;

                // The rest of the types are already defined, so those we do not have to worry
                // about.
                for &(element_loc, element) in path {
                    let member = type_.member(element).ok_or_else(|| {
                        ctx.errors.error(
                            element_loc,
                            format!(
                                "'{}' is not a field of '{}'(aliases do not allow dereferencing currently)",
                                element, type_
                            ),
                        )
                    })?;

                    offset += member.byte_offset;
                    type_ = member.type_;
                }

                resolved_aliases.push(Alias {
                    name: alias_name,
                    offset,
                    indirections,
                    type_,
                });
            }

            let type_ = Type::new_named(
                ctx.ast.get(parsed).loc,
                name,
                TypeKind::Struct(typed_fields),
                resolved_aliases,
            );
            let type_type = Type::new(TypeKind::Type);

            Node::new(
                ctx.ast.get(parsed).loc,
                NodeKind::Constant(
                    ctx.program.insert_buffer(
                        type_type,
                        &(type_.as_ptr() as usize).to_le_bytes() as *const _,
                    ),
                    None,
                ),
                type_type,
            )
        }
        ParsedNodeKind::LiteralType(_)
        | ParsedNodeKind::ArrayType { .. }
        | ParsedNodeKind::StructType { .. }
        | ParsedNodeKind::FunctionType { .. }
        | ParsedNodeKind::BufferType(_)
        | ParsedNodeKind::ReferenceType { .. } => {
            ctx.errors.error(
                ctx.ast.get(parsed).loc,
                "(Internal compiler error) The parser should not emit a type node here".to_string(),
            );
            return Err(());
        }
    };

    if !wanted_type.type_fits(node.type_()) {
        if let Some(loc) = wanted_type.loc {
            ctx.errors
                .info(loc, "Expected type came from here".to_string());
        }

        ctx.errors.error(
            ctx.ast.get(parsed).loc,
            format!("Expected '{}', found '{}'", wanted_type, node.type_()),
        );
        return Err(());
    }

    Ok(node)
}

/// An 'lvalue' is something you're assigning to, or something you're referencing. Basically, it's
/// not just a value, but a value at a specific location, either in a variable, in memory, or
/// similar. For example, *pointer may just be the number 3, but if you were to do *pointer = 5,
/// the '*pointer' here also cares about the location of that number, and not just the value.
fn make_sure_valid_lvalue(
    ctx: &mut Context<'_, '_>,
    typed: &Node,
    required_permits: PtrPermits,
) -> Result<(), ()> {
    // Right now, this only really validates that it's a valid lvalue, but it doesn't do anything
    // different. In the future, we may want to migrate some of that logic from the emit.rs file
    // into here, but I'm not sure.

    if typed.type_().size() == 0 {
        // Zero sized types can always be referenced.
        return Ok(());
    }

    match typed.kind() {
        NodeKind::Member { ref of, .. } => make_sure_valid_lvalue(ctx, of, required_permits),
        NodeKind::Unary {
            op: UnaryOp::Dereference,
            ref operand,
        } => {
            if let TypeKind::Reference { permits, .. } = *operand.type_().kind() {
                if !permits.superset(required_permits) {
                    ctx.errors.error(
                        typed.loc,
                        format!(
                            "Required {} permissions, but the type '{}' only allows {}",
                            required_permits,
                            operand.type_(),
                            permits
                        ),
                    );
                    Err(())
                } else {
                    Ok(())
                }
            } else {
                unreachable!("This should not happen because this is called after typing, and the typing should catch it")
            }
        }
        NodeKind::Global { .. } | NodeKind::Constant { .. } => {
            if required_permits.write() {
                ctx.errors.error(
                    typed.loc,
                    "Cannot modify a global value, or take a non-constant reference to it"
                        .to_string(),
                );
                return Err(());
            }

            Ok(())
        }
        NodeKind::Local(_) => {
            // @Improvement: We should check if it will modify it, and return an error if this is
            // an immutable variable
            Ok(())
        }
        _ => {
            // ctx.errors.error(typed.loc, "Not an lvalue, which is required here.\nTry breaking it out into a local variable first and then referencing that instead, maybe.".to_string());

            if required_permits.write() {
                ctx.errors.error(typed.loc, "Cannot assign or take mutable references to temporary values, put this in a variable first".to_string());
                return Err(());
            }

            // @Cleanup: This is a little weird, but basically, we can create a temporary value and
            // just reference that in most cases. That's dealt with the emitter. The reason lvalues
            // are validated is because of mutability
            Ok(())
        }
    }
}

fn const_fold_type_expr<'a>(
    ctx: &mut Context<'a, '_>,
    parsed: ParsedNodeId,
    buffer: &mut SelfBuffer,
) -> Result<Type, ()> {
    match ctx.ast.get(parsed).kind {
        ParsedNodeKind::PolymorphicArgument(index) => {
            let (arg_type, arg_value) = ctx.poly_args[index];

            if let TypeKind::Type = arg_type.kind() {
                Ok(unsafe { *arg_value.as_ptr().cast::<Type>() })
            } else {
                ctx.errors
                    .error(ctx.ast.get(parsed).loc, "This is not a type".to_string());
                Err(())
            }
        }
        ParsedNodeKind::GlobalForTyping(scope, name, ref poly_args) => {
            let id = ctx.program.get_member_id(scope, name).unwrap();
            let id = monomorphise(
                ctx,
                ctx.ast.get(parsed).loc,
                name,
                id,
                MemberDep::ValueAndCallableIfFunction,
                poly_args,
                buffer,
            )?;

            let ptr = ctx.program.get_value_of_member(id).as_ptr();
            Ok(unsafe { *ptr.cast::<Type>() })
        }
        ParsedNodeKind::LiteralType(type_) => Ok(type_),
        ParsedNodeKind::StructType {
            fields: ref parsed_fields,
        } => {
            let mut fields = Vec::with_capacity(parsed_fields.len());
            for &(name, parsed_field_type) in parsed_fields {
                let field_type = const_fold_type_expr(ctx, parsed_field_type, buffer)?;
                fields.push((name, field_type));
            }
            Ok(Type::new(TypeKind::Struct(fields)))
        }
        ParsedNodeKind::BufferType(internal) => {
            let pointee = const_fold_type_expr(ctx, internal, buffer)?;
            Ok(Type::new(TypeKind::Buffer(pointee)))
        }
        ParsedNodeKind::ArrayType {
            len,
            members,
        } => {
            let len = type_ast(
                ctx,
                WantedType::specific(None, Type::new(TypeKind::Int(IntTypeKind::Usize))),
                len,
                buffer,
            )?;

            if let NodeKind::Constant(len, _) = len.kind() {
                let length = unsafe { *len.as_ptr().cast::<usize>() };

                let member = const_fold_type_expr(ctx, members, buffer)?;
                Ok(Type::new(TypeKind::Array(member, length)))
            } else {
                ctx.errors
                    .error(len.loc, "Expected constant expression".to_string());
                Err(())
            }
        }
        ParsedNodeKind::ReferenceType(internal, permits) => {
            let pointee = const_fold_type_expr(ctx, internal, buffer)?;
            Ok(Type::new(TypeKind::Reference { pointee, permits }))
        }
        ParsedNodeKind::FunctionType {
            ref args,
            returns,
        } => {
            let mut arg_types = Vec::with_capacity(args.len());
            for &arg in args {
                arg_types.push(const_fold_type_expr(ctx, arg, buffer)?);
            }

            let returns = const_fold_type_expr(ctx, returns, buffer)?;

            Ok(TypeKind::Function {
                args: arg_types,
                returns,
            }
            .into())
        }
        _ => {
            ctx.errors.error(
                ctx.ast.get(parsed).loc,
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
    ctx: &mut Context<'a, '_>,
    loc: Location,
    from: Node,
    to_type: Type,
    buffer: &mut SelfBuffer,
) -> Result<Node, ()> {
    if from.type_() == to_type {
        ctx.errors.warning(
            loc,
            format!(
                "You don't need a cast here, because '{}' and '{}' are the same types",
                from.type_(),
                to_type
            ),
        );
        return Ok(from);
    }

    match (from.type_().kind(), to_type.kind()) {
        (
            TypeKind::Reference {
                pointee:
                    Type(TypeData {
                        kind: TypeKind::Array(from_inner, len),
                        ..
                    }),
                ..
            },
            TypeKind::Buffer(to_inner),
        ) if from_inner == to_inner => Ok(Node::new(
            loc,
            NodeKind::ArrayToBuffer {
                length: *len,
                array: buffer.insert(from),
            },
            to_type,
        )),
        (TypeKind::Reference { .. }, TypeKind::Int(IntTypeKind::Usize)) => Ok(Node::new(
            loc,
            NodeKind::BitCast {
                value: buffer.insert(from),
            },
            to_type,
        )),
        (TypeKind::Reference { pointee, .. }, TypeKind::AnyPtr) => Ok(Node::new(
            loc,
            NodeKind::PtrToAny {
                ptr: buffer.insert(from),
                type_: *pointee,
            },
            to_type,
        )),
        (TypeKind::Reference { .. }, TypeKind::VoidPtr) => Ok(Node::new(
            loc,
            NodeKind::BitCast {
                value: buffer.insert(from),
            },
            to_type,
        )),
        (TypeKind::VoidPtr, TypeKind::Reference { .. }) => Ok(Node::new(
            loc,
            NodeKind::BitCast {
                value: buffer.insert(from),
            },
            to_type,
        )),
        (TypeKind::VoidBuffer, TypeKind::Buffer(inner)) => Ok(Node::new(
            loc,
            NodeKind::VoidToBuffer {
                any: buffer.insert(from),
                inner: *inner,
            },
            to_type,
        )),
        (TypeKind::Buffer(inner), TypeKind::VoidBuffer) => Ok(Node::new(
            loc,
            NodeKind::BufferToVoid {
                buffer: buffer.insert(from),
                inner: *inner,
            },
            to_type,
        )),
        (
            TypeKind::Reference {
                pointee:
                    Type(TypeData {
                        kind: TypeKind::Array(from_inner, len),
                        ..
                    }),
                permits: from_permits,
            },
            TypeKind::Reference {
                pointee: to_inner,
                permits: to_permits,
            },
        ) if from_inner == to_inner && from_permits.superset(*to_permits) && *len > 0 => {
            Ok(Node::new(
                loc,
                NodeKind::BitCast {
                    value: buffer.insert(from),
                },
                to_type,
            ))
        }
        (_, _) => {
            ctx.errors.error(
                loc,
                format!("No cast available for '{}' to '{}'", from.type_(), to_type),
            );
            Err(())
        }
    }
}

fn monomorphise<'a>(
    ctx: &mut Context<'a, '_>,
    loc: Location,
    name: Ustr,
    id: PolyOrMember,
    needed_evaluation: MemberDep,
    poly_args: &'a [ParsedNodeId],
    buffer: &mut SelfBuffer,
) -> Result<MemberId, ()> {
    match id {
        PolyOrMember::Member(id) => {
            if !poly_args.is_empty() {
                ctx.errors.error(
                    loc,
                    format!(
                        "Polymorphic arguments were not expected; '{}' is not polymorphic",
                        name
                    ),
                );
                return Err(());
            }

            Ok(id)
        }
        PolyOrMember::Poly(id) => {
            let num_args = ctx.program.get_num_poly_args(id);

            let mut evaluated_poly_args = Vec::with_capacity(poly_args.len());
            for &arg in poly_args {
                let result = type_ast(ctx, WantedType::none(), arg, buffer)?;

                if let NodeKind::Constant(value, _) = result.kind() {
                    evaluated_poly_args.push((result.type_(), *value));
                } else {
                    ctx.errors.error(
                        ctx.ast.get(arg).loc,
                        "Expected constant value, use 'const' if you want a complicated expression"
                            .to_string(),
                    );
                    return Err(());
                }
            }

            if evaluated_poly_args.len() != num_args {
                ctx.errors.error(
                    loc,
                    format!(
                        "Expected '{}' polymorphic arguments, got '{}'",
                        num_args,
                        evaluated_poly_args.len()
                    ),
                );
                return Err(());
            }

            ctx.program.monomorphise_poly_member(
                ctx.errors,
                ctx.thread_context,
                id,
                &evaluated_poly_args,
                needed_evaluation,
            )
        }
    }
}
