use crate::ir::{Member, Registers, Routine, UserDefinedRoutine, Value};
use crate::location::Location;
use crate::literal::Literal;
use crate::locals::LocalVariables;
use crate::operators::{BinaryOp, UnaryOp};
use crate::parser::{Ast, NodeKind, NodeView};
use crate::ast::NodeId;
use crate::program::{FunctionId, Program};
use crate::thread_pool::ThreadContext;
use crate::type_infer::{ValueId as TypeId, TypeSystem, Reason, Args, AstVariantId, self};
use crate::typer::{AdditionalInfo, AdditionalInfoKind, FunctionArgUsage};
use crate::types::{Type, TypeKind, IntTypeKind};

mod context;
use context::Context;

/// Emit instructions for an Ast.
pub fn emit<'a>(
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    locals: &mut LocalVariables,
    types: &mut TypeSystem,
    ast: &Ast,
    additional_info: &AdditionalInfo,
    node: NodeId,
    variant_id: AstVariantId,
) -> (Vec<FunctionId>, UserDefinedRoutine) {
    let mut ctx = Context {
        thread_context,
        instr: Vec::new(),
        registers: Registers::new(),
        locals,
        types,
        program,
        label_locations: Vec::new(),
        calling: Vec::new(),
        last_location: None,
        variant_id,
        additional_info,

        defers: Vec::new(),
    };

    let result = emit_node(&mut ctx, ast.get(node));

    /*println!("The instructions are: ");
    for instr in &ctx.instr {
        println!("{:?}", instr);
    }*/

    (
        ctx.calling,
        UserDefinedRoutine {
            loc: ast.root().loc,
            instr: ctx.instr,
            registers: ctx.registers,
            result,
            label_locations: ctx.label_locations,
        },
    )
}

pub fn emit_function_declaration<'a>(
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    locals: &mut LocalVariables,
    types: &mut TypeSystem,
    ast: &Ast,
    additional_info: &AdditionalInfo,
    node_id: NodeId,
    variant_id: AstVariantId,
    type_: Type,
    loc: Location,
    function_id: FunctionId,
) {
    let mut ctx = Context {
        thread_context,
        instr: Vec::new(),
        registers: Registers::new(),
        locals,
        types,
        program,
        variant_id,
        label_locations: Vec::new(),
        defers: Vec::new(),
        calling: Vec::new(),
        last_location: None,
        additional_info,
    };

    let function_type = ctx.types.get(TypeId::Node(ctx.variant_id, node_id));
    let args = function_type.args();

    debug_assert_eq!(function_type.kind(), &type_infer::TypeKind::Function);

    // Pretend there are actual values on the stack
    let arg_values: Vec<_> = args.iter().skip(1).map(|&v| {
        ctx.registers.create(ctx.types, v)
    }).collect();

    let node = ast.get(node_id);
    let mut children = node.children.into_iter();
    for passed_as in arg_values.into_iter() {
        let child = children.next().unwrap();
        emit_declarative_lvalue(&mut ctx, child, passed_as, true);
    }

    // Now that we've read all the arguments of the function, only the return type,
    // and the body are left. We don't need the return type, as that is only for the typer,
    // so we skip that one.

    let result = emit_node(&mut ctx, children.nth(1).unwrap());

    /*println!("The instructions are: ");
    for instr in &ctx.instr {
        println!("{:?}", instr);
    }*/

    let routine = Routine::UserDefined(UserDefinedRoutine {
        loc,
        label_locations: ctx.label_locations,
        instr: ctx.instr,
        registers: ctx.registers,
        result,
    });

    if ctx.program.arguments.release {
        if let TypeKind::Function { args, returns } = type_.kind() {
            crate::c_backend::function_declaration(
                &mut ctx.thread_context.c_headers,
                crate::c_backend::c_format_function(function_id),
                args,
                *returns,
            );

            ctx.thread_context.c_headers.push_str(";\n");

            crate::c_backend::function_declaration(
                &mut ctx.thread_context.c_declarations,
                crate::c_backend::c_format_function(function_id),
                args,
                *returns,
            );
            ctx.thread_context.c_declarations.push_str(" {\n");

            crate::c_backend::routine_to_c(
                ctx.program,
                &mut ctx.thread_context.c_declarations,
                &routine,
                args,
                *returns,
            );
            ctx.thread_context.c_declarations.push_str("}\n");
        } else {
            unreachable!("A function type node has to have a function type kind!!!!!!");
        }
    }

    ctx
        .program
        .set_routine_of_function(function_id, ctx.calling, routine);
}

fn emit_node<'a>(ctx: &mut Context<'a, '_>, mut node: NodeView<'a>) -> Value {
    ctx.emit_debug(node.loc);

    let node_type_id = TypeId::Node(ctx.variant_id, node.id);

    match &node.kind {
        NodeKind::Empty => ctx.registers.zst(),
        NodeKind::Break {
            label: label_id,
            num_defer_deduplications,
        } => {
            let [value] = node.children.as_array();
            
            let label = ctx.locals.get_label(*label_id);
            let ir_label = label.ir_labels.as_ref().unwrap()[*num_defer_deduplications];
            let label_value = label.value.unwrap();

            let from = emit_node(ctx, value);

            for defer_index in (ctx.locals.get_label(*label_id).defer_depth
                + *num_defer_deduplications..ctx.defers.len())
                .rev()
            {
                emit_node(ctx, ctx.defers[defer_index].clone());
            }

            ctx.emit_move(label_value, from);
            ctx.emit_jump(ir_label);

            ctx.registers.zst()
        }
        NodeKind::For {
            is_const: Some(_),
            label,
        } => {
            let [iterating, i_value_decl, mut inner, else_body] = node.children.as_array();

            let AdditionalInfoKind::ConstForAstVariants(variants) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };

            let end_label = ctx.create_label();

            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            ctx.locals.get_label_mut(*label).value = Some(to);

            // Set up iterator values
            let i_value = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, i_value_decl.id));
            ctx.emit_move_from_constant(i_value, &0_usize.to_le_bytes());

            let iterating_value = emit_node(ctx, iterating.clone());
            let base_iterator_type = ctx.types.value_to_compiler_type(TypeId::Node(ctx.variant_id, iterating.id));
            for (i, &variant_id) in variants.iter().enumerate() {
                emit_declarative_lvalue(ctx, i_value_decl.clone(), i_value, true);

                let [v_value_decl, body] = inner.children.as_array();

                let temp_iterator_value = ctx.registers.create(ctx.types, TypeId::Node(variant_id, v_value_decl.id));
                let (name, offset, _) = base_iterator_type.0.members[i];
                ctx.emit_member(temp_iterator_value, iterating_value, Member { offset, name });

                let old_variant_id = ctx.variant_id;
                ctx.variant_id = variant_id;
                emit_declarative_lvalue(ctx, v_value_decl, temp_iterator_value, true);
                emit_node(ctx, body);
                ctx.variant_id = old_variant_id;

                ctx.emit_increment(i_value);
            }

            let evaluate_to = emit_node(ctx, else_body);
            ctx.emit_move(to, evaluate_to);
            ctx.define_label(end_label);
            evaluate_to
        }
        NodeKind::For {
            is_const: None,
            label,
        } => {
            let [iterating, i_value_decl, mut inner, else_body] = node.children.as_array();
            let [v_value_decl, body] = inner.children.as_array();

            let end_label = ctx.create_label();
            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            ctx.locals.get_label_mut(*label).value = Some(to);
            ctx.locals.get_label_mut(*label).ir_labels = Some(vec![end_label]);

            let mut iterating_value = emit_node(ctx, iterating.clone());

            // Set up iterator values
            let i_value = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, i_value_decl.id));
            ctx.emit_move_from_constant(i_value, &0_usize.to_le_bytes());

            let mut by_value = true;

            let mut iterator_type_id = TypeId::Node(ctx.variant_id, iterating.id);
            if let type_infer::TypeKind::Reference = ctx.types.get(iterator_type_id).kind() {
                iterator_type_id = ctx.types.get(iterator_type_id).args()[0];
                by_value = false;
            }

            let (current, end) = match ctx.types.get(iterator_type_id).kind() {
                type_infer::TypeKind::Array => {
                    let iterator_type = ctx.types.get(iterator_type_id);
                    let iterator_args = iterator_type.args();
                    let element_type = iterator_args[0];
                    let length = ctx.types.extract_constant_temp(iterator_args[1]).unwrap();

                    let ptr_to_array = if by_value {
                        let array_ptr_type_id = ctx.types.add_type(type_infer::TypeKind::Reference, type_infer::Args([(iterator_type_id, Reason::temp_zero())]), ());
                        let temp = ctx.registers.create(ctx.types, array_ptr_type_id);
                        ctx.emit_reference(temp, iterating_value);
                        temp
                    } else {
                        iterating_value
                    };

                    let element_ptr_type = ctx.types.add_type(type_infer::TypeKind::Reference, type_infer::Args([(element_type, Reason::temp_zero())]), ());
                    let first_element = ctx.registers.create(ctx.types, element_ptr_type);
                    let last_element = ctx.registers.create(ctx.types, element_ptr_type);
                    ctx.emit_bitcast(first_element, ptr_to_array);

                    let usize_type = ctx.types.add_int(IntTypeKind::Usize, ());
                    let len_reg = ctx.registers.create(ctx.types, usize_type);
                    ctx.emit_global(len_reg, length);
                    ctx.emit_binary(BinaryOp::Add, last_element, first_element, len_reg);

                    (first_element, last_element)
                }
                type_infer::TypeKind::Buffer => {
                    let pointee = ctx.types.get(iterator_type_id).args()[0];

                    if !by_value {
                        let new_iterating = ctx.registers.create(ctx.types, iterator_type_id);
                        ctx.emit_dereference(new_iterating, iterating_value);
                        iterating_value = new_iterating;
                    }

                    let iteration_type_id = ctx.types.add_type(type_infer::TypeKind::Reference, type_infer::Args([(pointee, type_infer::Reason::temp_zero())]), ());

                    let current = ctx.registers.create(ctx.types, iteration_type_id);
                    let end = ctx.registers.create(ctx.types, iteration_type_id);

                    ctx.emit_member(
                        current,
                        iterating_value,
                        Member {
                            offset: 0,
                            name: "ptr".into(),
                        },
                    );

                    let usize_type = ctx.types.add_int(IntTypeKind::Usize, ());
                    let len = ctx
                        .registers
                        .create(ctx.types, usize_type);
                    ctx.emit_member(
                        len,
                        iterating_value,
                        Member {
                            offset: 8,
                            name: "len".into(),
                        },
                    );

                    ctx.emit_binary(BinaryOp::Add, end, current, len);

                    (current, end)
                }
                _ => unreachable!(),
            };

            let bool_type = ctx.types.add_type(type_infer::TypeKind::Bool, Args([]), ());
            let condition = ctx.registers.create(ctx.types, bool_type);

            let condition_label = ctx.create_label();
            ctx.define_label(condition_label);

            ctx.emit_binary(BinaryOp::LessThan, condition, current, end);

            let else_body_label = ctx.create_label();
            ctx.emit_jump_if_zero(condition, else_body_label);

            emit_declarative_lvalue(ctx, i_value_decl, i_value, true);

            if by_value {
                let temp = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, v_value_decl.id));
                ctx.emit_dereference(temp, current);
                emit_declarative_lvalue(ctx, v_value_decl, temp, true);
            } else {
                emit_declarative_lvalue(ctx, v_value_decl, current, true);
            }
            emit_node(ctx, body);
            ctx.emit_increment(current);

            ctx.emit_increment(i_value);

            ctx.emit_jump(condition_label);

            ctx.define_label(else_body_label);

            let else_body_from = emit_node(ctx, else_body);
            ctx.emit_move(to, else_body_from);

            ctx.define_label(end_label);

            to
        }
        NodeKind::While {
            label,
        } => {
            let [i_value_decl, condition, body, else_body] = node.children.as_array();

            let end_label = ctx.create_label();
            let else_body_label = ctx.create_label();

            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            let label = ctx.locals.get_label_mut(*label);
            label.value = Some(to);
            label.ir_labels = Some(vec![end_label]);

            let i_value = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, i_value_decl.id)); 
            ctx.emit_move_from_constant(i_value, &0_usize.to_le_bytes());

            // Condition
            let condition_label = ctx.create_label();
            ctx.define_label(condition_label);

            emit_declarative_lvalue(ctx, i_value_decl, i_value, true);

            let condition = emit_node(ctx, condition);
            ctx.emit_jump_if_zero(condition, else_body_label);

            // Loop body
            emit_node(ctx, body);
            ctx.emit_increment(i_value);
            ctx.emit_jump(condition_label);

            // Else body
            ctx.define_label(else_body_label);

            let else_body_value = emit_node(ctx, else_body);
            ctx.emit_move(to, else_body_value);

            // End
            ctx.define_label(end_label);

            to
        }
        NodeKind::If {
            is_const: None,
        } => {
            let [condition, true_body, false_body] = node.children.as_array();

            let condition = emit_node(ctx, condition);

            let start_of_false_body = ctx.create_label();
            let end_of_false_body = ctx.create_label();

            ctx.emit_jump_if_zero(condition, start_of_false_body);

            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));

            // True body
            let true_body = emit_node(ctx, true_body);
            ctx.emit_move(to, true_body);
            ctx.emit_jump(end_of_false_body);

            // False body
            ctx.define_label(start_of_false_body);
            let false_body = emit_node(ctx, false_body);
            ctx.emit_move(to, false_body);

            ctx.define_label(end_of_false_body);

            to
        }
        NodeKind::Literal(Literal::String(data)) => {
            let u8_type = Type::new(TypeKind::Int(IntTypeKind::U8));
            let type_ = Type::new(TypeKind::Buffer { pointee: u8_type });
            let ptr = ctx.program.insert_buffer(
                type_,
                &crate::types::BufferRepr {
                    ptr: data.as_ptr() as *mut _,
                    length: data.len(),
                } as *const _ as *const _,
            );

            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_global(to, ptr);
            to
        }
        NodeKind::Literal(Literal::Int(num)) => {
            let bytes = num.to_le_bytes();

            let buffer = ctx.program.insert_buffer(ctx.types.value_to_compiler_type(TypeId::Node(ctx.variant_id, node.id)), bytes.as_ptr());

            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_global(to, buffer);

            to
        }
        &NodeKind::Literal(Literal::Float(num)) => {
            let type_ = ctx.types.value_to_compiler_type(TypeId::Node(ctx.variant_id, node.id));
            match type_.size() {
                4 => {
                    let bytes = (num as f32).to_bits().to_le_bytes();

                    let buffer = ctx.program.insert_buffer(type_, bytes.as_ptr());

                    let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
                    ctx.emit_global(to, buffer);

                    to
                }
                8 => {
                    let bytes = num.to_bits().to_le_bytes();

                    let buffer = ctx.program.insert_buffer(type_, bytes.as_ptr());

                    let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
                    ctx.emit_global(to, buffer);

                    to
                }
                _ => unreachable!(),
            }
        }
        NodeKind::Zeroed => {
            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_set_to_zero(to);
            to
        }
        NodeKind::Uninit => {
            // We don't need an instruction to initialize the memory, because it's uninit!
            ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id))
        }
        NodeKind::Cast => {
            let [value] = node.children.as_array();
            let from = emit_node(ctx, value.clone());
            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));

            // Get the types of the values
            let node_type = ctx.types.get(TypeId::Node(ctx.variant_id, node.id));
            let value_type = ctx.types.get(TypeId::Node(ctx.variant_id, value.id));

            match (node_type.kind, value_type.kind) {
                (
                    Some(type_infer::Type { kind: type_infer::TypeKind::Int, args: Some(to_args) }),
                    Some(type_infer::Type { kind: type_infer::TypeKind::Int, args: Some(_) }),
                ) => {
                    let is_signed_to = 0 < unsafe { *ctx.types.extract_constant_temp(to_args[0]).unwrap().as_ptr().cast::<u8>() };
                    let to_size = node_type.layout.unwrap().size;
                    let from_size = value_type.layout.unwrap().size;

                    if to_size <= from_size {
                        ctx.emit_truncate_int(to, from, to_size as u8);
                    } else {
                        ctx.emit_extend_int(to, from, to_size as u8, from_size as u8, is_signed_to);
                    }
                }
                (
                    Some(type_infer::Type { kind: type_infer::TypeKind::Buffer, args: Some(buf_args) }),
                    Some(type_infer::Type { kind: type_infer::TypeKind::Reference, args: Some(from_args) })
                ) => {
                    match ctx.types.get(from_args[0]).kind {
                        Some(type_infer::Type { kind: type_infer::TypeKind::Array, args: Some(array_args) }) => {
                            let buf_args_0 = buf_args[0];

                            let length = ctx.types.extract_constant_temp(array_args[1]).unwrap();
                            let usize_type = ctx.types.add_int(IntTypeKind::Usize, ());
                            let len_reg = ctx.registers.create(ctx.types, usize_type);

                            // @HACK: Yuck!!!
                            let temp_ptr_type = ctx.types.add_type(type_infer::TypeKind::Reference, type_infer::Args([(buf_args_0, Reason::temp_zero())]), ());
                            let temp_ptr = ctx.registers.create(ctx.types, temp_ptr_type);

                            ctx.emit_global(len_reg, length);
                            ctx.emit_bitcast(temp_ptr, from);

                            ctx.emit_move_to_member_of_value(
                                to,
                                temp_ptr,
                                Member {
                                    offset: 0,
                                    name: "ptr".into(),
                                },
                            );
                            ctx.emit_move_to_member_of_value(
                                to,
                                len_reg,
                                Member {
                                    offset: 8,
                                    name: "len".into(),
                                },
                            );
                        }
                        _ => unreachable!("Internal error: Invalid types for cast reached emission"),
                    }
                }
                (
                    Some(type_infer::Type { kind: type_infer::TypeKind::Reference, .. }),
                    Some(type_infer::Type { kind: type_infer::TypeKind::Reference, .. }),
                ) => {
                    // References are the same layout, we just do the same as with bitcast.
                    ctx.emit_bitcast(to, from);
                }
                _ => unreachable!("Internal error: Invalid types for cast reached emission"),
            }

            to
        }
        NodeKind::BitCast => {
            let [value] = node.children.as_array();
            let from = emit_node(ctx, value);
            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_move(to, from);
            to
        }
        NodeKind::Constant(bytes, _) => {
            if let type_infer::TypeKind::Function { .. } = ctx.types.get(TypeId::Node(ctx.variant_id, node.id)).kind() {
                let function_id = unsafe { *(bytes.as_ptr() as *const FunctionId) };
                if !ctx.calling.contains(&function_id) {
                    ctx.calling.push(function_id);
                }
            }

            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_global(to, *bytes);

            to
        }
        NodeKind::Member { name } => {
            let [of] = node.children.as_array();
            let mut of_type_id = TypeId::Node(ctx.variant_id, of.id);
            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            let mut of = emit_node(ctx, of);
            if let Some(type_infer::Type { kind: type_infer::TypeKind::Reference, args }) = ctx.types.get(of_type_id).kind {
                of_type_id = args.as_ref().unwrap()[0];
                let new_reg = ctx.registers.create(ctx.types, of_type_id);
                ctx.emit_dereference(new_reg, of);
                of = new_reg;
            }

            let Some(member) = of.type_().member(*name) else {
                unreachable!("Type {} doesn't have member {}, but it got through the typer", of.type_(), *name)
            };

            debug_assert_eq!(member.indirections, 1);

            ctx.emit_member(
                to,
                of,
                Member {
                    offset: member.byte_offset,
                    name: *name,
                },
            );
            to
        }
        NodeKind::Binary {
            op: BinaryOp::Assign,
        } => {
            let [to, from] = node.children.as_array();
            let from = emit_node(ctx, from);
            emit_declarative_lvalue(ctx, to, from, false);

            let empty_result = ctx.registers.zst();
            empty_result
        }
        NodeKind::Binary { op } => {
            let [left, right] = node.children.as_array();
            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));

            let a = emit_node(ctx, left);
            let b = emit_node(ctx, right);

            ctx.emit_binary(*op, to, a, b);

            to
        }
        NodeKind::Tuple => {
            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            let base_type = ctx.types.value_to_compiler_type(TypeId::Node(ctx.variant_id, node.id));

            for (i, child) in node.children.into_iter().enumerate() {
                let child_value = emit_node(ctx, child);

                let (name, offset, _) = base_type.0.members[i];
                ctx.emit_move_to_member_of_value(to, child_value, Member { offset, name });
            }

            to
        }
        NodeKind::ArrayLiteral => {
            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            let base_type = ctx.types.value_to_compiler_type(TypeId::Node(ctx.variant_id, node.id));

            for (i, child) in node.children.into_iter().enumerate() {
                let child_value = emit_node(ctx, child);

                let (name, offset, _) = base_type.0.members[i];
                ctx.emit_move_to_member_of_value(to, child_value, Member { offset, name });
            }

            to
        }
        NodeKind::Reference => {
            let [operand] = node.children.as_array();
            emit_lvalue(ctx, true, operand)
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            let [operand] = node.children.as_array();
            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            let from = emit_node(ctx, operand);
            ctx.emit_dereference(to, from);
            to
        }
        NodeKind::Unary { op } => {
            let [operand] = node.children.as_array();
            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            let from = emit_node(ctx, operand);
            ctx.emit_unary(*op, to, from);
            to
        }
        NodeKind::Local { local_id, .. } => {
            ctx.locals.get(*local_id).value.unwrap()
        }
        NodeKind::ConstAtEvaluation { .. } => {
            // TODO: Implement this, it's not going to work yet because emission cannot produce errors,
            // and assertion failures are errors.
            todo!()
            /*let type_ = ctx.ast.get(*inner).type_();
            let constant =
                crate::interp::emit_and_run(ctx.thread_context, ctx.program, ctx.locals, &ctx.ast, *inner);
            Value::Global(constant, type_)*/
        }
        NodeKind::Defer => {
            let [deferring] = node.children.as_array();
            ctx.defers.push(deferring);
            ctx.registers.zst()
        }
        NodeKind::Block { label } => {
            let num_defers_at_start = ctx.defers.len();

            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));

            if let Some(label) = *label {
                let ir_labels = (0..=ctx.locals.get_label(label).num_defers)
                    .map(|_| ctx.create_label())
                    .collect();
                let label_ref = ctx.locals.get_label_mut(label);
                label_ref.ir_labels = Some(ir_labels);
                label_ref.value = Some(to);
            }

            let head = ctx.registers.get_head();

            let mut children = node.children.into_iter();
            for content in children.by_ref().take(node.children.len() - 1) {
                emit_node(ctx, content);
            }

            let from = emit_node(ctx, children.next().unwrap());
            ctx.emit_move(to, from);

            for (i, defer_index) in (num_defers_at_start..ctx.defers.len()).enumerate().rev() {
                if let Some(label) = *label {
                    let ir_label = ctx.locals.get_label(label).ir_labels.as_ref().unwrap()[i + 1];
                    ctx.define_label(ir_label);
                }

                let defer = ctx.defers[defer_index].clone();
                emit_node(ctx, defer);
            }

            if let Some(label) = *label {
                let ir_label = ctx.locals.get_label(label).ir_labels.as_ref().unwrap()[0];
                ctx.define_label(ir_label);
            }

            ctx.defers.truncate(num_defers_at_start);

            ctx.registers.set_head(head);
            to
        }
        NodeKind::ResolvedGlobal(id, _) => {
            let (ptr, _) = ctx.program.get_member_value(*id);

            if let type_infer::TypeKind::Function = ctx.types.get(TypeId::Node(ctx.variant_id, node.id)).kind() {
                let function_id = unsafe { *(ptr.as_ptr() as *const FunctionId) };
                if !ctx.calling.contains(&function_id) {
                    ctx.calling.push(function_id);
                }
            }

            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_global(to, ptr);
            to
        }
        NodeKind::FunctionCall => {
            let mut children = node.children.into_iter();
            let calling_node = children.next().unwrap();

            let to = ctx.registers.create_min_align(ctx.types.value_to_compiler_type(TypeId::Node(ctx.variant_id, node.id)), 8);
            let calling = emit_node(ctx, calling_node.clone());
            let calling_type = ctx.types.get(TypeId::Node(ctx.variant_id, calling_node.id));
            let output_args = calling_type.args().iter().skip(1).map(|&v| {
                ctx.registers.create(ctx.types, v)
            }).collect::<Vec<_>>();

            if let Some(AdditionalInfoKind::FunctionCall(args)) = ctx.additional_info.get(&(ctx.variant_id, node.id)) {
                debug_assert_eq!(args.len(), children.len());
                for (arg, node) in args.iter().zip(children) {
                    match *arg {
                        FunctionArgUsage::ValueOfAssign { function_arg } => {
                            let [_, right] = node.children.into_array();
                            let given = emit_node(ctx, right);

                            ctx.emit_move(output_args[function_arg], given);
                        }
                        FunctionArgUsage::Value { function_arg } => {
                            let given = emit_node(ctx, node);

                            ctx.emit_move(output_args[function_arg], given);
                        }
                        FunctionArgUsage::TupleElement { function_arg, field } => {
                            let given = emit_node(ctx, node);

                            let calling_type = ctx.types.get(TypeId::Node(ctx.variant_id, calling_node.id));
                            let arg_type_id = calling_type.args()[function_arg + 1];
                            let (name, offset, _) = ctx.types.value_to_compiler_type(arg_type_id).0.members[field];
                            ctx.emit_move_to_member_of_value(output_args[function_arg], given, Member { offset, name });
                        }
                    }
                }
            } else {
                for (to, node) in output_args.iter().zip(children) {
                    let given = emit_node(ctx, node);
                    ctx.emit_move(*to, given);
                }
            }

            ctx.emit_call(to, calling, output_args, calling_node.loc);

            to
        }
        NodeKind::TypeBound { .. } => {
            let [value, _] = node.children.as_array();
            emit_node(ctx, value)
        }
        NodeKind::Parenthesis | NodeKind::Explain => {
            let [value] = node.children.as_array();
            emit_node(ctx, value)
        }
        NodeKind::SizeOf => {
            let [inner] = node.children.as_array();
            let inner_type = TypeId::Node(ctx.variant_id, inner.id);
            let size = ctx.types.get(inner_type).layout.unwrap().size;

            let to = ctx.registers.create(ctx.types, node_type_id);
            ctx.emit_move_from_constant(to, &size.to_le_bytes());
            to
        }
        NodeKind::TypeAsValue => {
            let [inner] = node.children.as_array();
            let inner_type = TypeId::Node(ctx.variant_id, inner.id);
            let compiler_type = ctx.types.value_to_compiler_type(inner_type);
            let constant_ref = ctx.program.insert_buffer(Type::new(TypeKind::Type), &compiler_type as *const _ as *const u8);

            let to = ctx.registers.create(ctx.types, node_type_id);
            ctx.emit_global(to, constant_ref);
            to
        }
        NodeKind::PolymorphicArgument(_) => {
            let &AdditionalInfoKind::Constant(constant) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };
            let inner_type = TypeId::Node(ctx.variant_id, node.id);
            let to = ctx.registers.create(ctx.types, inner_type);
            ctx.emit_global(to, constant);
            to
        }
        NodeKind::If {
            is_const: Some(_),
        } => {
            let [_, true_body, false_body] = node.children.as_array();

            let &AdditionalInfoKind::ConstIfResult(result) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };
            if result {
                emit_node(ctx, true_body)
            } else {
                emit_node(ctx, false_body)
            }
        }
        NodeKind::PolymorphicArgs { .. } | NodeKind::Global { .. } => {
            let &AdditionalInfoKind::Monomorphised(id) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };

            let (ptr, _) = ctx.program.get_member_value(id);

            if let type_infer::TypeKind::Function = ctx.types.get(TypeId::Node(ctx.variant_id, node.id)).kind() {
                let function_id = unsafe { *(ptr.as_ptr() as *const FunctionId) };
                if !ctx.calling.contains(&function_id) {
                    ctx.calling.push(function_id);
                }
            }

            let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_global(to, ptr);
            to
        }
        NodeKind::BuiltinFunction(_) | NodeKind::FunctionDeclaration { .. } => {
            let &AdditionalInfoKind::Function(id) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };

            let inner_type = TypeId::Node(ctx.variant_id, node.id);
            let compiler_type = ctx.types.value_to_compiler_type(inner_type);
            let constant_ref = ctx.program.insert_buffer(compiler_type, &id as *const _ as *const u8);

            let to = ctx.registers.create(ctx.types, inner_type);
            ctx.emit_global(to, constant_ref);
            to
        }
        NodeKind::Is => {
            let to = ctx.registers.create(ctx.types, node_type_id);
           
            let &AdditionalInfoKind::IsExpression(comparison_id) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };
            let value = ctx.types.get_comparison_result(comparison_id);
            let compiler_type = ctx.types.value_to_compiler_type(node_type_id);
            let constant_ref = ctx.program.insert_buffer(compiler_type, &(value as u8) as *const u8);
            ctx.emit_global(to, constant_ref);
            to
        }
        c => unreachable!("This node should not reach emission: {:?}", c),
    }
}

fn emit_declarative_lvalue<'a>(
    ctx: &mut Context<'a, '_>,
    mut node: NodeView<'a>,
    from: Value,
    is_declaring: bool,
) {
    ctx.emit_debug(node.loc);

    match &node.kind {
        NodeKind::Member { .. } => {
            debug_assert!(!is_declaring);

            let to = emit_lvalue(ctx, false, node);
            ctx.emit_indirect_move(to, from);
        }
        NodeKind::Binary { op: BinaryOp::BitAnd } => {
            let [left, right] = node.children.into_array();

            emit_declarative_lvalue(ctx, left, from, is_declaring);
            emit_declarative_lvalue(ctx, right, from, is_declaring);
        }
        NodeKind::ImplicitType => {}
        NodeKind::Declare => {
            let [value] = node.children.as_array();
            emit_declarative_lvalue(ctx, value, from, true);
        }
        NodeKind::Tuple => {
            let base_type = ctx.types.value_to_compiler_type(TypeId::Node(ctx.variant_id, node.id));

            let mut temp = Vec::with_capacity(node.children.len());
            for (i, child) in node.children.into_iter().enumerate() {
                let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, child.id));
                let (name, offset, _) = base_type.0.members[i];
                ctx.emit_member(to, from, Member { offset, name });
                temp.push(to);
            }

            for (child, to) in node.children.into_iter().zip(temp) {
                emit_declarative_lvalue(ctx, child, to, is_declaring);
            }
        }
        NodeKind::ArrayLiteral => {
            let base_type = ctx.types.value_to_compiler_type(TypeId::Node(ctx.variant_id, node.id));

            let mut temp = Vec::with_capacity(node.children.len());
            for (i, child) in node.children.into_iter().enumerate() {
                let to = ctx.registers.create(ctx.types, TypeId::Node(ctx.variant_id, child.id));
                let (name, offset, _) = base_type.0.members[i];
                ctx.emit_member(to, from, Member { offset, name });
                temp.push(to);
            }

            for (child, to) in node.children.into_iter().zip(temp) {
                emit_declarative_lvalue(ctx, child, to, is_declaring);
            }
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            debug_assert!(!is_declaring);
            let [operand] = node.children.as_array();
            let pointer = emit_node(ctx, operand);
            ctx.emit_indirect_move(pointer, from);
        }
        NodeKind::Local { local_id, .. } => {
            if is_declaring {
                let local = ctx.locals.get_mut(*local_id);
                let local_value = ctx.registers.create_with_name(ctx.types, TypeId::Node(ctx.variant_id, local.declared_at.unwrap()), Some(local.name));
                local.value = Some(local_value);
                ctx.emit_move(local_value, from);
            } else {
                let to = ctx.locals.get(*local_id).value.unwrap();
                ctx.emit_move(to, from);
            }
        }
        NodeKind::Parenthesis => {
            let [value] = node.children.as_array();
            emit_declarative_lvalue(ctx, value, from, is_declaring);
        }
        NodeKind::TypeBound => {
            let [value, _] = node.children.as_array();
            emit_declarative_lvalue(ctx, value, from, is_declaring);
        }
        kind => {
            unreachable!(
                "{:?} is not an lvalue. This is just something I haven't implemented checking for in the compiler yet",
                kind
            )
        }
    }
}

fn emit_lvalue<'a>(
    ctx: &mut Context<'a, '_>,
    can_reference_temporaries: bool,
    mut node: NodeView<'a>,
) -> Value {
    ctx.emit_debug(node.loc);

    // @TODO: Creating all these types suck, maybe we should remove the damn `Global` thing from registers,
    // and instead let them just be pointers to values? These pointers wouldn't even be considered pointers from
    // the language, but just registers that need to point to things.
    let ref_type_id = ctx.types.add_type(type_infer::TypeKind::Reference, Args([(TypeId::Node(ctx.variant_id, node.id), Reason::temp_zero())]), ());

    match &node.kind {
        NodeKind::Member { name } => {
            let [of] = node.children.as_array();

            // If `of` is a reference, we need to do stuff.
            let (base_type, parent_value) = if let Some(type_infer::Type { kind: type_infer::TypeKind::Reference, args }) = ctx.types.get(TypeId::Node(ctx.variant_id, of.id)).kind {
                let arg = args.as_ref().unwrap()[0];
                (ctx.types.value_to_compiler_type(arg), emit_node(ctx, of))
            } else {
                let parent_value = emit_lvalue(ctx, can_reference_temporaries, of.clone());
                (ctx.types.value_to_compiler_type(TypeId::Node(ctx.variant_id, of.id)), parent_value)
            };

            let member = base_type.member(*name).expect("This should have already been made sure to exist in the typer");

            let to = ctx.registers.create(ctx.types, ref_type_id);
            ctx.emit_pointer_to_member_of_pointer(to, parent_value, Member { offset: member.byte_offset, name: *name });
            to
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            let [operand] = node.children.as_array();
            emit_node(ctx, operand)
        }
        NodeKind::Local { local_id, .. } => {
            let to = ctx.registers.create(ctx.types, ref_type_id);
            let from = ctx.locals.get(*local_id).value.unwrap();
            ctx.emit_reference(to, from);
            to
        }
        NodeKind::ResolvedGlobal(id, _) => {
            let to = ctx.registers.create(ctx.types, ref_type_id);
            let (from_ref, from_type) = ctx.program.get_member_value(*id);
            ctx.emit_ref_to_global(to, from_ref, from_type);
            to
        }
        NodeKind::Parenthesis => {
            let [value] = node.children.as_array();
            emit_lvalue(ctx, can_reference_temporaries, value)
        }
        NodeKind::TypeBound => {
            let [value, _] = node.children.as_array();
            emit_lvalue(ctx, can_reference_temporaries, value)
        }
        kind => {
            if can_reference_temporaries {
                let to = ctx.registers.create(ctx.types, ref_type_id);
                let from = emit_node(ctx, node);
                ctx.emit_reference(to, from);
                to
            } else {
                unreachable!(
                    "{:?} is not an lvalue. This is just something I haven't implemented checking for in the compiler yet",
                    kind
                )
            }
        }
    }
}
