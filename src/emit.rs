use crate::ir::{Member, Registers, Routine, UserDefinedRoutine, Value};
use crate::location::Location;
use crate::literal::Literal;
use crate::locals::LocalVariables;
use crate::operators::{BinaryOp, UnaryOp};
use crate::parser::{Ast, NodeKind, NodeView};
use crate::ast::NodeId;
use crate::program::{FunctionId, Program};
use crate::thread_pool::ThreadContext;
use crate::type_infer::{ValueId as TypeId, TypeSystem, Reason, Args, self};
use crate::types::{Type, TypeKind};

mod context;
use context::Context;

/// Emit instructions for an Ast.
pub fn emit<'a>(
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    locals: &mut LocalVariables,
    types: &mut TypeSystem,
    ast: &Ast,
    node: NodeId,
    stack_frame_id: crate::type_infer::ValueSetId,
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

        defers: Vec::new(),
    };

    // Allocate registers for all the locals
    for local in ctx.locals.iter_mut() {
        if local.stack_frame_id == stack_frame_id {
            let value = ctx.registers.create_with_name(ctx.types, local.type_infer_value_id, local.type_.unwrap(), Some(local.name));
            local.value = Some(value);
        }
    }

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
    node_id: NodeId,
    type_: Type,
    loc: Location,
    function_id: FunctionId,
    stack_frame_id: crate::type_infer::ValueSetId,
) {
    let mut sub_ctx = Context {
        thread_context,
        instr: Vec::new(),
        registers: Registers::new(),
        locals,
        types,
        program,
        label_locations: Vec::new(),
        defers: Vec::new(),
        calling: Vec::new(),
        last_location: None,
    };

    // Allocate registers for all the locals
    for local in sub_ctx.locals.iter_mut() {
        if local.stack_frame_id == stack_frame_id {
            let value = sub_ctx.registers.create_with_name(sub_ctx.types, local.type_infer_value_id, local.type_.unwrap(), Some(local.name));
            local.value = Some(value);
        }
    }

    let result = emit_node(&mut sub_ctx, ast.get(node_id));

    let routine = Routine::UserDefined(UserDefinedRoutine {
        loc,
        label_locations: sub_ctx.label_locations,
        instr: sub_ctx.instr,
        registers: sub_ctx.registers,
        result,
    });

    if sub_ctx.program.arguments.release {
        if let TypeKind::Function { args, returns } = type_.kind() {
            crate::c_backend::function_declaration(
                &mut sub_ctx.thread_context.c_headers,
                crate::c_backend::c_format_function(function_id),
                args,
                *returns,
            );

            sub_ctx.thread_context.c_headers.push_str(";\n");

            crate::c_backend::function_declaration(
                &mut sub_ctx.thread_context.c_declarations,
                crate::c_backend::c_format_function(function_id),
                args,
                *returns,
            );
            sub_ctx.thread_context.c_declarations.push_str(" {\n");

            crate::c_backend::routine_to_c(
                sub_ctx.program,
                &mut sub_ctx.thread_context.c_declarations,
                &routine,
                args,
                *returns,
            );
            sub_ctx.thread_context.c_declarations.push_str("}\n");
        } else {
            unreachable!("A function type node has to have a function type kind!!!!!!");
        }
    }

    sub_ctx
        .program
        .set_routine_of_function(function_id, sub_ctx.calling, routine);
}

fn emit_node<'a>(ctx: &mut Context<'a, '_>, mut node: NodeView<'a>) -> Value {
    ctx.emit_debug(node.loc);

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
            iterator,
            iteration_var,
            label,
        } => {
            let [iterating, body, else_body] = node.children.as_array();

            let end_label = ctx.create_label();
            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));
            ctx.locals.get_label_mut(*label).value = Some(to);
            ctx.locals.get_label_mut(*label).ir_labels = Some(vec![end_label]);

            let mut iterating_value = emit_node(ctx, iterating.clone());

            let iterator_local = ctx.locals.get_mut(*iterator);
            let iterator_type_id = iterator_local.type_infer_value_id;

            let iterator_value = ctx.registers.create(ctx.types, iterator_type_id);
            iterator_local.value = Some(iterator_value);

            // Set up iterator values
            let iteration_var_value = if ctx.locals.get(*iteration_var).num_uses > 0 {
                let reg = ctx
                    .registers
                    .create(ctx.types, type_infer::static_values::USIZE);
                ctx.locals.get_mut(*iteration_var).value = Some(reg);
                ctx.emit_move_from_constant(reg, &0_usize.to_le_bytes());
                Some(reg)
            } else {
                None
            };

            let mut by_value = true;

            let mut iterator_type_id = TypeId::Node(iterating.id);
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

                    let len_reg = ctx.registers.create(ctx.types, type_infer::static_values::USIZE);
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

                    let len = ctx
                        .registers
                        .create(ctx.types, type_infer::static_values::USIZE);
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

            let condition = ctx.registers.create(ctx.types, type_infer::static_values::BOOL);

            let condition_label = ctx.create_label();
            ctx.define_label(condition_label);

            ctx.emit_binary(BinaryOp::LessThan, condition, current, end);

            let else_body_label = ctx.create_label();
            ctx.emit_jump_if_zero(condition, else_body_label);

            if by_value {
                ctx.emit_dereference(iterator_value, current);
            } else {
                ctx.emit_move(iterator_value, current);
            }
            emit_node(ctx, body);
            ctx.emit_increment(current);

            if let Some(iteration_var_value) = iteration_var_value {
                ctx.emit_increment(iteration_var_value);
            }

            ctx.emit_jump(condition_label);

            ctx.define_label(else_body_label);

            let else_body_from = emit_node(ctx, else_body);
            ctx.emit_move(to, else_body_from);

            ctx.define_label(end_label);

            to
        }
        NodeKind::While {
            iteration_var,
            label,
        } => {
            let [condition, body, else_body] = node.children.as_array();

            let end_label = ctx.create_label();
            let else_body_label = ctx.create_label();

            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));
            let label = ctx.locals.get_label_mut(*label);
            label.value = Some(to);
            label.ir_labels = Some(vec![end_label]);

            let iteration_var_mut = ctx.locals.get_mut(*iteration_var);
            let iteration_var_value = if iteration_var_mut.num_uses > 0 {
                let reg = ctx
                    .registers
                    .create(ctx.types, type_infer::static_values::USIZE);
                iteration_var_mut.value = Some(reg);
                ctx.emit_move_from_constant(reg, &0_usize.to_le_bytes());
                Some(reg)
            } else {
                None
            };

            // Condition
            let condition_label = ctx.create_label();
            ctx.define_label(condition_label);

            let condition = emit_node(ctx, condition);
            ctx.emit_jump_if_zero(condition, else_body_label);

            // Loop body
            emit_node(ctx, body);
            if let Some(iteration_var_value) = iteration_var_value {
                ctx.emit_increment(iteration_var_value);
            }
            ctx.emit_jump(condition_label);

            // Else body
            ctx.define_label(else_body_label);

            let else_body_value = emit_node(ctx, else_body);
            ctx.emit_move(to, else_body_value);

            // End
            ctx.define_label(end_label);

            to
        }
        NodeKind::ConditionalCompilation { child } => {
            let child = node.children.into_iter().nth(*child).unwrap();
            emit_node(ctx, child)
        }
        NodeKind::If {
            is_const,
        } => {
            debug_assert!(is_const.is_none(), "const ifs should be dealt with in the typer");

            let [condition, true_body, false_body] = node.children.as_array();

            let condition = emit_node(ctx, condition);

            let start_of_false_body = ctx.create_label();
            let end_of_false_body = ctx.create_label();

            ctx.emit_jump_if_zero(condition, start_of_false_body);

            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));

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
        NodeKind::Literal(Literal::Int(num)) => {
            let bytes = num.to_le_bytes();

            let buffer = ctx.program.insert_buffer(ctx.types.value_to_compiler_type(TypeId::Node(node.id)), bytes.as_ptr());

            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));
            ctx.emit_global(to, buffer);

            to
        }
        NodeKind::Zeroed => {
            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));
            ctx.emit_set_to_zero(to);
            to
        }
        NodeKind::Uninit => {
            // We don't need an instruction to initialize the memory, because it's uninit!
            ctx.registers.create(ctx.types, TypeId::Node(node.id))
        }
        NodeKind::Cast => {
            let [value] = node.children.as_array();
            let from = emit_node(ctx, value.clone());
            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));

            // Get the types of the values
            let node_type = ctx.types.get(TypeId::Node(node.id));
            let value_type = ctx.types.get(TypeId::Node(value.id));

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
                            let length = ctx.types.extract_constant_temp(array_args[1]).unwrap();
                            let len_reg = ctx.registers.create(ctx.types, type_infer::static_values::USIZE);

                            // @HACK: Yuck!!!
                            let buf_args_0 = buf_args[0];
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
            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));
            ctx.emit_move(to, from);
            to
        }
        NodeKind::Constant(bytes, _) => {
            if let type_infer::TypeKind::Function { .. } = ctx.types.get(TypeId::Node(node.id)).kind() {
                let function_id = unsafe { *(bytes.as_ptr() as *const FunctionId) };
                if !ctx.calling.contains(&function_id) {
                    ctx.calling.push(function_id);
                }
            }

            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));
            ctx.emit_global(to, *bytes);

            to
        }
        NodeKind::Member { name } => {
            let [of] = node.children.as_array();
            let mut of_type_id = TypeId::Node(of.id);
            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));
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
            let to = emit_lvalue(ctx, false, to);
            let from = emit_node(ctx, from);

            let empty_result = ctx.registers.zst();
            ctx.emit_indirect_move(to, from);
            empty_result
        }
        NodeKind::Binary { op } => {
            let [left, right] = node.children.as_array();
            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));

            let a = emit_node(ctx, left);
            let b = emit_node(ctx, right);

            ctx.emit_binary(*op, to, a, b);

            to
        }
        NodeKind::Tuple => {
            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));
            let base_type = ctx.types.value_to_compiler_type(TypeId::Node(node.id));

            for (i, child) in node.children.into_iter().enumerate() {
                let child_value = emit_node(ctx, child);

                let (name, offset, _) = base_type.0.members[i];
                ctx.emit_move_to_member_of_value(to, child_value, Member { offset, name });
            }

            to
        }
        NodeKind::ArrayLiteral => {
            let node_type = ctx.types.get(TypeId::Node(node.id));
            let internal_type =
                if let type_infer::TypeKind::Array = node_type.kind() {
                    node_type.kind.as_ref().unwrap().args.as_ref().unwrap()[0]
                } else {
                    unreachable!()
                };

            let internal_type_node = ctx.types.get(TypeId::Node(node.id));
            let Some(type_infer::Type { kind: type_infer::TypeKind::Array, args: Some(internal_type_args) }) = &internal_type_node.kind else {
                unreachable!()
            };

            // This is a bit weird but it has to be checked here. The reason is we generate a temporary pointer to the elements
            // of the array, and this internal pointer does not account for the array being zero sized; i.e., getting a non zero
            // sized pointer from a zero sized type.
            if node.children.len() > 0 && ctx.types.get(internal_type).layout.unwrap().size > 0 {
                let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));
                let internal_type_arg = internal_type_args[0];
                let ref_type_id = ctx.types.add_type(type_infer::TypeKind::Reference, Args([(internal_type_arg, Reason::temp_zero())]), ()); 
                let reference = ctx.registers.create(ctx.types, ref_type_id);
                ctx.emit_reference(reference, to);
                for (i, element) in node.children.into_iter().enumerate() {
                    if i > 0 {
                        ctx.emit_increment(reference);
                    }
                    let from = emit_node(ctx, element);
                    ctx.emit_indirect_move(reference, from);
                }
                to
            } else {
                ctx.registers.zst()
            }
        }
        NodeKind::Reference => {
            let [operand] = node.children.as_array();
            emit_lvalue(ctx, true, operand)
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            let [operand] = node.children.as_array();
            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));
            let from = emit_node(ctx, operand);
            ctx.emit_dereference(to, from);
            to
        }
        NodeKind::Unary { op } => {
            let [operand] = node.children.as_array();
            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));
            let from = emit_node(ctx, operand);
            ctx.emit_unary(*op, to, from);
            to
        }
        NodeKind::Declare {
            local: id,
        } => {
            let [value] = node.children.as_array();
            let from = emit_node(ctx, value.clone());
            let to = ctx.registers.create(ctx.types, TypeId::Node(value.id));
            ctx.locals.get_mut(*id).value = Some(to);
            ctx.emit_move(to, from);
            to
        }
        NodeKind::Local(id) => ctx.locals.get(*id).value.unwrap(),
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

            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));

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

            if let type_infer::TypeKind::Function = ctx.types.get(TypeId::Node(node.id)).kind() {
                let function_id = unsafe { *(ptr.as_ptr() as *const FunctionId) };
                if !ctx.calling.contains(&function_id) {
                    ctx.calling.push(function_id);
                }
            }

            let to = ctx.registers.create(ctx.types, TypeId::Node(node.id));
            ctx.emit_global(to, ptr);
            to
        }
        NodeKind::ResolvedFunctionCall { arg_indices } => {
            let mut children = node.children.into_iter();
            let calling_node = children.next().unwrap();

            let to = ctx.registers.create_min_align(ctx.types.value_to_compiler_type(TypeId::Node(node.id)), 8);
            let calling = emit_node(ctx, calling_node.clone());

            let mut args = vec![ctx.registers.zst(); node.children.len() - 1];
            for (&i, node) in arg_indices.iter().zip(children) {
                args[i] = emit_node(ctx, node);
            }

            match ctx.types.get(TypeId::Node(calling_node.id)).kind() {
                type_infer::TypeKind::Function => {
                    ctx.emit_call(to, calling, args, calling_node.loc);
                }
                _ => todo!("The emitter doesn't know how to emit this type of call"),
            }
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
        c => unreachable!("This node should not reach emission: {:?}", c),
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
    let ref_type_id = ctx.types.add_type(type_infer::TypeKind::Reference, Args([(TypeId::Node(node.id), Reason::temp_zero())]), ());

    match &node.kind {
        NodeKind::Member { name } => {
            let [of] = node.children.as_array();

            // If `of` is a reference, we need to do stuff.
            let (base_type, parent_value) = if let Some(type_infer::Type { kind: type_infer::TypeKind::Reference, args }) = ctx.types.get(TypeId::Node(of.id)).kind {
                let arg = args.as_ref().unwrap()[0];
                (ctx.types.value_to_compiler_type(arg), emit_node(ctx, of))
            } else {
                let parent_value = emit_lvalue(ctx, can_reference_temporaries, of.clone());
                (ctx.types.value_to_compiler_type(TypeId::Node(of.id)), parent_value)
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
        NodeKind::Local(id) => {
            let to = ctx.registers.create(ctx.types, ref_type_id);
            let from = ctx.locals.get(*id).value.unwrap();
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
