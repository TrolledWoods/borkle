use crate::ir::{Member, Registers, Routine, UserDefinedRoutine, Value};
use crate::literal::Literal;
use crate::locals::LocalVariables;
use crate::operators::{BinaryOp, UnaryOp};
use crate::parser::ast::{Ast, NodeId, NodeKind};
use crate::program::{FunctionId, Program};
use crate::thread_pool::ThreadContext;
use crate::types::{IntTypeKind, PtrPermits, Type, TypeKind};

mod context;
use context::Context;

/// Emit instructions for an Ast.
pub fn emit<'a>(
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    locals: &mut LocalVariables,
    ast: &Ast,
    node: NodeId,
    stack_frame_id: crate::type_infer::ValueSetId,
) -> (Vec<FunctionId>, UserDefinedRoutine) {
    let mut ctx = Context {
        thread_context,
        instr: Vec::new(),
        registers: Registers::new(),
        locals,
        program,
        label_locations: Vec::new(),
        calling: Vec::new(),
        ast,

        defers: Vec::new(),
    };

    // Allocate registers for all the locals
    for local in ctx.locals.iter_mut() {
        if local.stack_frame_id == stack_frame_id {
            let value = ctx.registers.create(local.type_.unwrap());
            local.value = Some(value);
        }
    }

    let result = emit_node(&mut ctx, node);

    (
        ctx.calling,
        UserDefinedRoutine {
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
    ast: &Ast,
    node_id: NodeId,
    type_: Type,
    function_id: FunctionId,
    stack_frame_id: crate::type_infer::ValueSetId,
) {
    let mut sub_ctx = Context {
        thread_context,
        instr: Vec::new(),
        registers: Registers::new(),
        locals,
        program,
        label_locations: Vec::new(),
        defers: Vec::new(),
        calling: Vec::new(),
        ast,
    };

    // Allocate registers for all the locals
    for local in sub_ctx.locals.iter_mut() {
        if local.stack_frame_id == stack_frame_id {
            let value = sub_ctx.registers.create(local.type_.unwrap());
            local.value = Some(value);
        }
    }

    let result = emit_node(&mut sub_ctx, node_id);

    let routine = Routine::UserDefined(UserDefinedRoutine {
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

fn emit_node<'a>(ctx: &mut Context<'a, '_>, node: NodeId) -> Value {
    match &ctx.ast.get(node).kind {
        NodeKind::Empty => ctx.registers.zst(),
        NodeKind::Break {
            label: label_id,
            num_defer_deduplications,
            value,
        } => {
            let label = ctx.locals.get_label(*label_id);
            let ir_label = label.ir_labels.as_ref().unwrap()[*num_defer_deduplications];
            let label_value = label.value.unwrap();

            let from = emit_node(ctx, *value);

            for defer_index in (ctx.locals.get_label(*label_id).defer_depth
                + *num_defer_deduplications..ctx.defers.len())
                .rev()
            {
                emit_node(ctx, ctx.defers[defer_index]);
            }

            ctx.emit_move(label_value, from);
            ctx.emit_jump(ir_label);

            ctx.registers.zst()
        }
        NodeKind::For {
            iterator,
            iteration_var,
            iterating,
            body,
            label,
            else_body,
        } => {
            let end_label = ctx.create_label();
            let to = ctx.registers.create(ctx.ast.get(node).type_());
            ctx.locals.get_label_mut(*label).value = Some(to);
            ctx.locals.get_label_mut(*label).ir_labels = Some(vec![end_label]);

            let iterating_value = emit_node(ctx, *iterating);

            let iterator_local = ctx.locals.get_mut(*iterator);
            let iterator_type = iterator_local.type_.unwrap();

            let iterator_value = ctx.registers.create(iterator_type);
            iterator_local.value = Some(iterator_value);

            // Set up iterator values
            let iteration_var_value = if ctx.locals.get(*iteration_var).num_uses > 0 {
                let reg = ctx
                    .registers
                    .create(Type::new(TypeKind::Int(IntTypeKind::Usize)));
                ctx.locals.get_mut(*iteration_var).value = Some(reg);
                ctx.emit_move_from_constant(reg, &0_usize.to_le_bytes());
                Some(reg)
            } else {
                None
            };

            let start = ctx.registers.create(iterator_type);
            let end = ctx.registers.create(iterator_type);

            match ctx.ast.get(*iterating).type_().kind() {
                TypeKind::Range(inner) => match inner.kind() {
                    TypeKind::Int(_) | TypeKind::Reference { .. } => {
                        ctx.emit_member(
                            start,
                            iterating_value,
                            Member {
                                // 'start' member
                                offset: 0,
                                amount: 1,
                            },
                        );
                        ctx.emit_member(
                            end,
                            iterating_value,
                            Member {
                                offset: inner.size(),
                                amount: 1,
                            },
                        );
                    }
                    _ => unreachable!(),
                },
                TypeKind::Buffer { .. } => {
                    ctx.emit_member(
                        start,
                        iterating_value,
                        Member {
                            offset: 0,
                            amount: 1,
                        },
                    );

                    let len = ctx
                        .registers
                        .create(Type::new(TypeKind::Int(IntTypeKind::Usize)));
                    ctx.emit_member(
                        len,
                        iterating_value,
                        Member {
                            offset: 8,
                            amount: 1,
                        },
                    );

                    ctx.emit_binary(BinaryOp::Add, end, start, len);
                }
                _ => unreachable!(),
            }

            let condition = ctx.registers.create(Type::new(TypeKind::Bool));

            let condition_label = ctx.create_label();
            ctx.define_label(condition_label);

            ctx.emit_binary(BinaryOp::LessThan, condition, start, end);

            let else_body_label = ctx.create_label();
            ctx.emit_jump_if_zero(condition, else_body_label);

            ctx.emit_move(iterator_value, start);
            emit_node(ctx, *body);
            ctx.emit_increment(start);

            if let Some(iteration_var_value) = iteration_var_value {
                ctx.emit_increment(iteration_var_value);
            }

            ctx.emit_jump(condition_label);

            ctx.define_label(else_body_label);
            if let Some(else_body) = else_body {
                let else_body_from = emit_node(ctx, *else_body);
                ctx.emit_move(to, else_body_from);
            }

            ctx.define_label(end_label);

            to
        }
        NodeKind::While {
            condition,
            iteration_var,
            body,
            else_body,
            label,
        } => {
            let end_label = ctx.create_label();
            let else_body_label = ctx.create_label();

            let to = ctx.registers.create(ctx.ast.get(node).type_());
            let label = ctx.locals.get_label_mut(*label);
            label.value = Some(to);
            label.ir_labels = Some(vec![end_label]);

            let iteration_var_mut = ctx.locals.get_mut(*iteration_var);
            let iteration_var_value = if iteration_var_mut.num_uses > 0 {
                let reg = ctx
                    .registers
                    .create(Type::new(TypeKind::Int(IntTypeKind::Usize)));
                iteration_var_mut.value = Some(reg);
                ctx.emit_move_from_constant(reg, &0_usize.to_le_bytes());
                Some(reg)
            } else {
                None
            };

            // Condition
            let condition_label = ctx.create_label();
            ctx.define_label(condition_label);

            let condition = emit_node(ctx, *condition);
            ctx.emit_jump_if_zero(condition, else_body_label);

            // Loop body
            emit_node(ctx, *body);
            if let Some(iteration_var_value) = iteration_var_value {
                ctx.emit_increment(iteration_var_value);
            }
            ctx.emit_jump(condition_label);

            // Else body
            ctx.define_label(else_body_label);
            if let Some(else_body) = else_body {
                let else_body_value = emit_node(ctx, *else_body);
                ctx.emit_move(to, else_body_value);
            }

            // End
            ctx.define_label(end_label);

            to
        }
        NodeKind::If {
            condition,
            true_body,
            false_body: None,
        } => {
            if let NodeKind::Constant(data, _) = ctx.ast.get(*condition).kind {
                if unsafe { *data.as_ptr() } != 0 {
                    emit_node(ctx, *true_body);
                }
            } else {
                let condition = emit_node(ctx, *condition);

                let end_of_body = ctx.create_label();
                ctx.emit_jump_if_zero(condition, end_of_body);

                emit_node(ctx, *true_body);

                ctx.define_label(end_of_body);
            }

            ctx.registers.zst()
        }
        NodeKind::If {
            condition,
            true_body,
            false_body: Some(false_body),
        } => {
            let condition = emit_node(ctx, *condition);

            let start_of_false_body = ctx.create_label();
            let end_of_false_body = ctx.create_label();

            ctx.emit_jump_if_zero(condition, start_of_false_body);

            let to = ctx.registers.create(ctx.ast.get(node).type_());

            // True body
            let true_body = emit_node(ctx, *true_body);
            ctx.emit_move(to, true_body);
            ctx.emit_jump(end_of_false_body);

            // False body
            ctx.define_label(start_of_false_body);
            let false_body = emit_node(ctx, *false_body);
            ctx.emit_move(to, false_body);

            ctx.define_label(end_of_false_body);

            to
        }
        NodeKind::Literal(Literal::Int(num)) => {
            let node_type = ctx.ast.get(node).type_();
            let bytes = num.to_le_bytes();

            // This is terrifying, if node_type isn't an int this will blow up.
            let buffer = ctx.program.insert_buffer(node_type, bytes.as_ptr());

            Value::Global(buffer, node_type)
        }
        NodeKind::Zeroed => {
            let to = ctx.registers.create(ctx.ast.get(node).type_());
            ctx.emit_set_to_zero(to);
            to
        }
        NodeKind::Uninit => {
            // We don't need an instruction to initialize the memory, because it's uninit!
            ctx.registers.create(ctx.ast.get(node).type_())
        }
        NodeKind::BitCast { value } => {
            let from = emit_node(ctx, *value);
            let to = ctx.registers.create(ctx.ast.get(node).type_());
            ctx.emit_move(to, from);
            to
        }
        NodeKind::PtrToAny { ptr, type_ } => {
            let ptr = emit_node(ctx, *ptr);

            let to = ctx.registers.create(ctx.ast.get(node).type_());
            ctx.emit_move_to_member_of_value(
                to,
                ptr,
                Member {
                    offset: 0,
                    amount: 1,
                },
            );

            let type_type = Type::new(TypeKind::Type);
            let type_ = ctx
                .program
                .insert_buffer(type_type, type_.as_id().to_le_bytes().as_ptr());

            ctx.emit_move_to_member_of_value(
                to,
                Value::Global(type_, type_type),
                Member {
                    offset: 8,
                    amount: 1,
                },
            );

            to
        }
        NodeKind::BufferToVoid { buffer, inner } => {
            let from = emit_node(ctx, *buffer);

            let ptr = ctx.registers.create(Type::new(TypeKind::VoidPtr));
            ctx.emit_member(
                ptr,
                from,
                Member {
                    offset: 0,
                    amount: 1,
                },
            );

            let usize_type = Type::new(TypeKind::Int(IntTypeKind::Usize));
            let len = ctx.registers.create(usize_type);
            ctx.emit_member(
                len,
                from,
                Member {
                    offset: 8,
                    amount: 1,
                },
            );

            let constant = ctx
                .program
                .insert_buffer(usize_type, inner.size().to_le_bytes().as_ptr());
            ctx.emit_binary(
                BinaryOp::Mult,
                len,
                len,
                Value::Global(constant, usize_type),
            );

            let to = ctx.registers.create(ctx.ast.get(node).type_());
            ctx.emit_move_to_member_of_value(
                to,
                len,
                Member {
                    offset: 8,
                    amount: 1,
                },
            );
            ctx.emit_move_to_member_of_value(
                to,
                ptr,
                Member {
                    offset: 0,
                    amount: 1,
                },
            );

            to
        }
        NodeKind::VoidToBuffer { any, inner } => {
            let from = emit_node(ctx, *any);

            let ptr = ctx.registers.create(Type::new(TypeKind::VoidPtr));
            ctx.emit_member(
                ptr,
                from,
                Member {
                    offset: 0,
                    amount: 1,
                },
            );

            let usize_type = Type::new(TypeKind::Int(IntTypeKind::Usize));
            let len = ctx.registers.create(usize_type);
            ctx.emit_member(
                len,
                from,
                Member {
                    offset: 8,
                    amount: 1,
                },
            );

            let constant = ctx
                .program
                .insert_buffer(usize_type, inner.size().to_le_bytes().as_ptr());
            ctx.emit_binary(BinaryOp::Div, len, len, Value::Global(constant, usize_type));

            let to = ctx.registers.create(ctx.ast.get(node).type_());
            ctx.emit_move_to_member_of_value(
                to,
                len,
                Member {
                    offset: 8,
                    amount: 1,
                },
            );
            ctx.emit_move_to_member_of_value(
                to,
                ptr,
                Member {
                    offset: 0,
                    amount: 1,
                },
            );

            to
        }
        NodeKind::ArrayToBuffer { length, array } => {
            let from = emit_node(ctx, *array);
            let to = ctx.registers.create(ctx.ast.get(node).type_());

            let len_reg = ctx
                .registers
                .create(Type::new(TypeKind::Int(IntTypeKind::Usize)));
            ctx.emit_move_from_constant(len_reg, &length.to_le_bytes());

            ctx.emit_move_to_member_of_value(
                to,
                from,
                Member {
                    offset: 0,
                    amount: 1,
                },
            );
            ctx.emit_move_to_member_of_value(
                to,
                len_reg,
                Member {
                    offset: 8,
                    amount: 1,
                },
            );
            to
        }
        NodeKind::Constant(bytes, _) => {
            if let TypeKind::Function { .. } = ctx.ast.get(node).type_().kind() {
                let function_id = unsafe { *(bytes.as_ptr() as *const FunctionId) };
                if !ctx.calling.contains(&function_id) {
                    ctx.calling.push(function_id);
                }
            }

            Value::Global(*bytes, ctx.ast.get(node).type_())
        }
        NodeKind::Member { name, of } => {
            let to = ctx.registers.create(ctx.ast.get(node).type_());
            let of = emit_node(ctx, *of);

            let member = of.type_().member(*name).unwrap();
            ctx.emit_member(
                to,
                of,
                Member {
                    offset: member.byte_offset,
                    amount: member.indirections,
                },
            );
            to
        }
        NodeKind::Binary {
            op: BinaryOp::Assign,
            left: lvalue,
            right: rvalue,
        } => {
            let to = emit_lvalue(ctx, false, *lvalue);
            let from = emit_node(ctx, *rvalue);

            let empty_result = ctx.registers.zst();

            match to {
                LValue::Reference(to, offset_to_target) => {
                    ctx.emit_move_to_member_of_pointer(to, from, offset_to_target);
                    empty_result
                }
                LValue::Value(to, offset_to_target) => {
                    ctx.emit_move_to_member_of_value(to, from, offset_to_target);
                    empty_result
                }
            }
        }
        NodeKind::Binary { op, left, right } => {
            let to = ctx.registers.create(ctx.ast.get(node).type_());

            let a = emit_node(ctx, *left);
            let b = emit_node(ctx, *right);

            ctx.emit_binary(*op, to, a, b);

            to
        }
        NodeKind::ArrayLiteral(elements) => {
            let internal_type =
                if let TypeKind::Array(internal, _) = ctx.ast.get(node).type_().kind() {
                    *internal
                } else {
                    unreachable!()
                };

            // This is a bit weird but it has to be checked here. The reason is we generate a temporary pointer to the elements
            // of the array, and this internal pointer does not account for the array being zero sized; i.e., getting a non zero
            // sized pointer from a zero sized type.
            if !elements.is_empty() && internal_type.size() > 0 {
                let to = ctx.registers.create(ctx.ast.get(node).type_());
                let ref_type = Type::new(TypeKind::Reference {
                    pointee: internal_type,
                    permits: PtrPermits::READ_WRITE,
                });
                let reference = ctx.registers.create(ref_type);
                ctx.emit_pointer_to_member_of_value(reference, to, Member::default());
                for (i, element) in elements.iter().enumerate() {
                    if i > 0 {
                        ctx.emit_increment(reference);
                    }
                    let from = emit_node(ctx, *element);
                    ctx.emit_indirect_move(reference, from);
                }
                to
            } else {
                ctx.registers.zst()
            }
        }
        NodeKind::Reference(operand) => {
            let to = ctx.registers.create(ctx.ast.get(node).type_());
            let from = emit_lvalue(ctx, true, *operand);
            match from {
                LValue::Reference(from, member) => {
                    ctx.emit_pointer_to_member_of_pointer(to, from, member);
                }
                LValue::Value(from, offset) => {
                    ctx.emit_pointer_to_member_of_value(to, from, offset);
                }
            }
            to
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
            operand,
        } => {
            let to = ctx.registers.create(ctx.ast.get(node).type_());
            let from = emit_node(ctx, *operand);
            ctx.emit_dereference(to, from);
            to
        }
        NodeKind::Unary { op, operand } => {
            let to = ctx.registers.create(ctx.ast.get(node).type_());
            let from = emit_node(ctx, *operand);
            ctx.emit_unary(*op, to, from);
            to
        }
        NodeKind::Declare {
            local: id,
            value,
            dummy_local_node: _,
        } => {
            let from = emit_node(ctx, *value);
            let to = ctx.registers.create(ctx.ast.get(*value).type_());
            ctx.locals.get_mut(*id).value = Some(to);
            ctx.emit_move(to, from);
            to
        }
        NodeKind::Local(id) => ctx.locals.get(*id).value.unwrap(),
        NodeKind::ConstAtEvaluation { inner } => {
            todo!();
            /*
            let type_ = ctx.ast.get(*inner).type_();
            let constant =
                crate::interp::emit_and_run(ctx.thread_context, ctx.program, locals.clone(), &ctx.ast, *inner);
            Value::Global(constant, type_)
            */
        }
        NodeKind::Defer { deferring } => {
            ctx.defers.push(*deferring);
            ctx.registers.zst()
        }
        NodeKind::Block { label, contents } => {
            let num_defers_at_start = ctx.defers.len();

            let to = ctx.registers.create(ctx.ast.get(node).type_());

            if let Some(label) = *label {
                let ir_labels = (0..=ctx.locals.get_label(label).num_defers)
                    .map(|_| ctx.create_label())
                    .collect();
                let label_ref = ctx.locals.get_label_mut(label);
                label_ref.ir_labels = Some(ir_labels);
                label_ref.value = Some(to);
            }

            let head = ctx.registers.get_head();

            for content in contents.iter().take(contents.len() - 1) {
                emit_node(ctx, *content);
            }

            let from = emit_node(ctx, *contents.last().unwrap());
            ctx.emit_move(to, from);

            for (i, defer_index) in (num_defers_at_start..ctx.defers.len()).enumerate().rev() {
                if let Some(label) = *label {
                    let ir_label = ctx.locals.get_label(label).ir_labels.as_ref().unwrap()[i + 1];
                    ctx.define_label(ir_label);
                }

                let defer = ctx.defers[defer_index];
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
            let (ptr, type_) = ctx.program.get_member_value(*id);

            if let TypeKind::Function { .. } = type_.kind() {
                let function_id = unsafe { *(ptr.as_ptr() as *const FunctionId) };
                if !ctx.calling.contains(&function_id) {
                    ctx.calling.push(function_id);
                }
            }

            Value::Global(ptr, type_)
        }
        NodeKind::ResolvedFunctionCall {
            calling: typed_calling,
            args: typed_args,
        } => {
            let to = ctx.registers.create_min_align(ctx.ast.get(node).type_(), 8);
            let calling = emit_node(ctx, *typed_calling);

            let mut args = vec![ctx.registers.zst(); typed_args.len()];
            for (i, arg) in typed_args {
                args[*i] = emit_node(ctx, *arg);
            }

            match ctx.ast.get(*typed_calling).type_().kind() {
                TypeKind::Function { .. } => {
                    ctx.emit_call(to, calling, args);
                }
                _ => todo!("The emitter doesn't know how to emit this type of call"),
            }
            to
        }
        NodeKind::TypeBound { value, bound: _ } | NodeKind::Parenthesis(value) => {
            emit_node(ctx, *value)
        }
        c => unreachable!("This node should not reach emission: {:?}", c),
    }
}

fn emit_lvalue<'a>(
    ctx: &mut Context<'a, '_>,
    can_reference_temporaries: bool,
    node: NodeId,
) -> LValue {
    match &ctx.ast.get(node).kind {
        NodeKind::Member { name, of } => {
            let parent_value = emit_lvalue(ctx, can_reference_temporaries, *of);

            let member = ctx
                .ast
                .get(*of)
                .type_()
                .member(*name)
                .expect("This should have already been made sure to exist in the typer");

            match parent_value {
                LValue::Reference(value, mut ref_member) => {
                    ref_member.offset += member.byte_offset;
                    ref_member.amount += member.indirections;
                    LValue::Reference(value, ref_member)
                }
                LValue::Value(value, mut ref_member) => {
                    ref_member.offset += member.byte_offset;
                    ref_member.amount += member.indirections;
                    LValue::Value(value, ref_member)
                }
            }
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
            operand,
        } => LValue::Reference(emit_node(ctx, *operand), Member::default()),
        NodeKind::Local(id) => LValue::Value(ctx.locals.get(*id).value.unwrap(), Member::default()),
        NodeKind::ResolvedGlobal(id, _) => {
            LValue::Value(ctx.program.get_constant_as_value(*id), Member::default())
        }
        kind => {
            if can_reference_temporaries {
                LValue::Value(emit_node(ctx, node), Member::default())
            } else {
                unreachable!(
                    "{:?} is not an lvalue. This is just something I haven't implemented checking for in the compiler yet",
                    kind
                )
            }
        }
    }
}

enum LValue {
    Reference(Value, Member),
    Value(Value, Member),
}
