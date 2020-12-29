use crate::ir::{Member, Registers, Routine, Value};
use crate::locals::LocalVariables;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::constant::ConstantRef;
use crate::program::thread_pool::ThreadContext;
use crate::program::Program;
use crate::typer::ast::NodeKind;
use crate::typer::Node;
use crate::types::{IntTypeKind, Type, TypeKind};

mod context;
use context::Context;

/// Emit instructions for an Ast.
pub fn emit<'a>(
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    locals: LocalVariables,
    ast: &Node,
) -> Routine {
    let mut ctx = Context {
        thread_context,
        instr: Vec::new(),
        registers: Registers::new(),
        locals,
        program,
        label_locations: Vec::new(),

        defers: Vec::new(),
    };

    // Allocate registers for all the locals
    for local in ctx.locals.iter_mut() {
        let value = ctx.registers.create(local.type_.unwrap());
        local.value = Some(value);
    }

    let result = emit_node(&mut ctx, ast);

    Routine {
        instr: ctx.instr,
        registers: ctx.registers,
        result,
        label_locations: ctx.label_locations,
    }
}

pub fn emit_function_declaration<'a>(
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    locals: LocalVariables,
    body: &Node,
    type_: Type,
) -> ConstantRef {
    let mut sub_ctx = Context {
        thread_context,
        instr: Vec::new(),
        registers: Registers::new(),
        locals,
        program,
        label_locations: Vec::new(),
        defers: Vec::new(),
    };

    // Allocate registers for all the locals
    for local in sub_ctx.locals.iter_mut() {
        let value = sub_ctx.registers.create(local.type_.unwrap());
        local.value = Some(value);
    }

    let result = emit_node(&mut sub_ctx, body);

    let routine = Routine {
        label_locations: sub_ctx.label_locations,
        instr: sub_ctx.instr,
        registers: sub_ctx.registers,
        result,
    };

    let id = sub_ctx.program.insert_function(routine);
    if sub_ctx.program.arguments.release {
        if let TypeKind::Function {
            args,
            returns,
            is_extern: false,
        } = type_.kind()
        {
            crate::c_backend::function_declaration(
                &mut sub_ctx.thread_context.c_headers,
                crate::c_backend::c_format_global(id),
                args,
                *returns,
            );
            crate::c_backend::function_declaration(
                &mut sub_ctx.thread_context.c_declarations,
                crate::c_backend::c_format_global(id),
                args,
                *returns,
            );

            sub_ctx.thread_context.c_headers.push_str(";\n");

            sub_ctx.thread_context.c_declarations.push_str(" {\n");
            crate::c_backend::routine_to_c(
                &mut sub_ctx.thread_context.c_declarations,
                unsafe { &*(id as *const Routine) },
                args.len(),
            );
            sub_ctx.thread_context.c_declarations.push_str("}\n");
        } else {
            unreachable!("A function type node has to have a function type kind!!!!!!");
        }
    }

    sub_ctx
        .program
        .insert_buffer(type_, id.to_le_bytes().as_ptr())
}

fn emit_node<'a>(ctx: &mut Context<'a, '_>, node: &'a Node) -> Value {
    match node.kind() {
        NodeKind::Break {
            label: label_id,
            num_defer_deduplications,
            value,
        } => {
            let label = ctx.locals.get_label(*label_id);
            let ir_label = label.ir_labels.as_ref().unwrap()[*num_defer_deduplications];
            let label_value = label.value.unwrap();

            let from = emit_node(ctx, value);

            for defer_index in (ctx.locals.get_label(*label_id).defer_depth
                + *num_defer_deduplications..ctx.defers.len())
                .rev()
            {
                emit_node(ctx, ctx.defers[defer_index]);
            }

            ctx.emit_move(label_value, from, Member::default());
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
            let to = ctx.registers.create(node.type_());
            ctx.locals.get_label_mut(*label).value = Some(to);
            ctx.locals.get_label_mut(*label).ir_labels = Some(vec![end_label]);

            let iterating_value = emit_node(ctx, iterating);

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
                ctx.emit_constant_from_buffer(reg, &0_usize.to_le_bytes());
                Some(reg)
            } else {
                None
            };

            let start = ctx.registers.create(iterator_type);
            let end = ctx.registers.create(iterator_type);

            match iterating.type_().kind() {
                TypeKind::Range(inner) => match inner.kind() {
                    TypeKind::Int(_) | TypeKind::Reference(_) => {
                        ctx.emit_member(
                            start,
                            iterating_value,
                            Member {
                                offset: 0,
                                name_list: vec!["start".into()],
                            },
                        );
                        ctx.emit_member(
                            end,
                            iterating_value,
                            Member {
                                offset: inner.size(),
                                name_list: vec!["end".into()],
                            },
                        );
                    }
                    _ => unreachable!(),
                },
                TypeKind::Buffer(_) => {
                    ctx.emit_member(
                        start,
                        iterating_value,
                        Member {
                            offset: 0,
                            name_list: vec!["ptr".into()],
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
                            name_list: vec!["len".into()],
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

            ctx.emit_move(iterator_value, start, Member::default());
            emit_node(ctx, body);
            ctx.emit_increment(start);

            if let Some(iteration_var_value) = iteration_var_value {
                ctx.emit_increment(iteration_var_value);
            }

            ctx.emit_jump(condition_label);

            ctx.define_label(else_body_label);
            if let Some(else_body) = else_body {
                let else_body_from = emit_node(ctx, else_body);
                ctx.emit_move(to, else_body_from, Member::default());
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

            let to = ctx.registers.create(node.type_());
            let label = ctx.locals.get_label_mut(*label);
            label.value = Some(to);
            label.ir_labels = Some(vec![end_label]);

            let iteration_var_mut = ctx.locals.get_mut(*iteration_var);
            let iteration_var_value = if iteration_var_mut.num_uses > 0 {
                let reg = ctx
                    .registers
                    .create(Type::new(TypeKind::Int(IntTypeKind::Usize)));
                iteration_var_mut.value = Some(reg);
                ctx.emit_constant_from_buffer(reg, &0_usize.to_le_bytes());
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
            if let Some(else_body) = else_body {
                let else_body_value = emit_node(ctx, else_body);
                ctx.emit_move(to, else_body_value, Member::default());
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
            if let NodeKind::Constant(data) = condition.kind() {
                if unsafe { *data.as_ptr() } != 0 {
                    emit_node(ctx, true_body);
                }
            } else {
                let condition = emit_node(ctx, condition);

                let end_of_body = ctx.create_label();
                ctx.emit_jump_if_zero(condition, end_of_body);

                emit_node(ctx, true_body);

                ctx.define_label(end_of_body);
            }

            ctx.registers.zst()
        }
        NodeKind::If {
            condition,
            true_body,
            false_body: Some(false_body),
        } => {
            let condition = emit_node(ctx, condition);

            let start_of_false_body = ctx.create_label();
            let end_of_false_body = ctx.create_label();

            ctx.emit_jump_if_zero(condition, start_of_false_body);

            let to = ctx.registers.create(node.type_());

            // True body
            let true_body = emit_node(ctx, true_body);
            ctx.emit_move(to, true_body, Member::default());
            ctx.emit_jump(end_of_false_body);

            // False body
            ctx.define_label(start_of_false_body);
            let false_body = emit_node(ctx, false_body);
            ctx.emit_move(to, false_body, Member::default());

            ctx.define_label(end_of_false_body);

            to
        }
        NodeKind::Uninit => {
            // We don't need an instruction to initialize the memory, because it's uninit!
            ctx.registers.create(node.type_())
        }
        NodeKind::FunctionDeclaration {
            locals,
            body,
            arg_names: _,
            default_values: _,
        } => {
            let function = emit_function_declaration(
                ctx.thread_context,
                ctx.program,
                locals.clone(),
                body,
                node.type_(),
            );

            let to = ctx.registers.create(node.type_());
            ctx.emit_constant_from_constant_buffer(to, function);
            to
        }
        NodeKind::BitCast { value } => {
            let from = emit_node(ctx, value);
            let to = ctx.registers.create(node.type_());
            ctx.emit_move(to, from, Member::default());
            to
        }
        NodeKind::BufferToAny { buffer, inner } => {
            let from = emit_node(ctx, buffer);

            let ptr = ctx.registers.create(Type::new(TypeKind::Any));
            ctx.emit_member(
                ptr,
                from,
                Member {
                    offset: 0,
                    name_list: vec!["ptr".into()],
                },
            );

            let usize_type = Type::new(TypeKind::Int(IntTypeKind::Usize));
            let len = ctx.registers.create(usize_type);
            ctx.emit_member(
                len,
                from,
                Member {
                    offset: 8,
                    name_list: vec!["len".into()],
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

            let to = ctx.registers.create(node.type_());
            ctx.emit_move(
                to,
                len,
                Member {
                    offset: 8,
                    name_list: vec!["len".into()],
                },
            );
            ctx.emit_move(
                to,
                ptr,
                Member {
                    offset: 0,
                    name_list: vec!["ptr".into()],
                },
            );

            to
        }
        NodeKind::AnyToBuffer { any, inner } => {
            let from = emit_node(ctx, any);

            let ptr = ctx.registers.create(Type::new(TypeKind::Any));
            ctx.emit_member(
                ptr,
                from,
                Member {
                    offset: 0,
                    name_list: vec!["ptr".into()],
                },
            );

            let usize_type = Type::new(TypeKind::Int(IntTypeKind::Usize));
            let len = ctx.registers.create(usize_type);
            ctx.emit_member(
                len,
                from,
                Member {
                    offset: 8,
                    name_list: vec!["len".into()],
                },
            );

            let constant = ctx
                .program
                .insert_buffer(usize_type, inner.size().to_le_bytes().as_ptr());
            ctx.emit_binary(BinaryOp::Div, len, len, Value::Global(constant, usize_type));

            let to = ctx.registers.create(node.type_());
            ctx.emit_move(
                to,
                len,
                Member {
                    offset: 8,
                    name_list: vec!["len".into()],
                },
            );
            ctx.emit_move(
                to,
                ptr,
                Member {
                    offset: 0,
                    name_list: vec!["ptr".into()],
                },
            );

            to
        }
        NodeKind::ArrayToBuffer { length, array } => {
            let from = emit_node(ctx, array);
            let to = ctx.registers.create(node.type_());

            let len_reg = ctx
                .registers
                .create(Type::new(TypeKind::Int(IntTypeKind::Usize)));
            ctx.emit_constant_from_buffer(len_reg, &length.to_le_bytes());

            ctx.emit_move(
                to,
                from,
                Member {
                    offset: 0,
                    name_list: vec!["ptr".into()],
                },
            );
            ctx.emit_move(
                to,
                len_reg,
                Member {
                    offset: 8,
                    name_list: vec!["len".into()],
                },
            );
            to
        }
        NodeKind::Constant(bytes) => {
            let to = ctx.registers.create(node.type_());
            ctx.emit_constant_from_constant_buffer(to, *bytes);
            to
        }
        NodeKind::Member { name, of } => {
            let to = ctx.registers.create(node.type_());
            let of = emit_node(ctx, of);
            ctx.emit_member(
                to,
                of,
                Member {
                    offset: of.type_().member(*name).unwrap().byte_offset,
                    name_list: vec![*name],
                },
            );
            to
        }
        NodeKind::Binary { op, left, right } => {
            let to = ctx.registers.create(node.type_());

            let a = emit_node(ctx, left);
            let b = emit_node(ctx, right);

            ctx.emit_binary(*op, to, a, b);

            to
        }
        NodeKind::ArrayLiteral { elements } => {
            let internal_type = if let TypeKind::Array(internal, _) = node.type_().kind() {
                *internal
            } else {
                unreachable!()
            };

            let to = ctx.registers.create(node.type_());
            let ref_type = Type::new(TypeKind::Reference(internal_type));
            let reference = ctx.registers.create(ref_type);
            ctx.emit_reference(reference, to, Member::default());
            for (i, element) in elements.iter().enumerate() {
                if i > 0 {
                    ctx.emit_increment(reference);
                }
                let from = emit_node(ctx, element);
                ctx.emit_move_indirect(reference, from, Member::default());
            }
            to
        }
        NodeKind::Unary {
            op: UnaryOp::Reference,
            operand,
        } => {
            let to = ctx.registers.create(node.type_());
            let from = emit_lvalue(ctx, true, operand);
            match from {
                LValue::Reference(from, member) => {
                    ctx.emit_member(to, from, member);
                }
                LValue::Value(from, offset) => {
                    ctx.emit_reference(to, from, offset);
                }
            }
            to
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
            operand,
        } => {
            let to = ctx.registers.create(node.type_());
            let from = emit_node(ctx, operand);
            ctx.emit_dereference(to, from);
            to
        }
        NodeKind::Unary { op, operand } => {
            let to = ctx.registers.create(node.type_());
            let from = emit_node(ctx, operand);
            ctx.emit_unary(*op, to, from);
            to
        }
        NodeKind::Assign { lvalue, rvalue } => {
            let to = emit_lvalue(ctx, false, lvalue);
            let from = emit_node(ctx, rvalue);

            let empty_result = ctx.registers.zst();

            match to {
                LValue::Reference(to, offset_to_target) => {
                    ctx.emit_move_indirect(to, from, offset_to_target);
                    empty_result
                }
                LValue::Value(to, offset_to_target) => {
                    ctx.emit_move(to, from, offset_to_target);
                    empty_result
                }
            }
        }
        NodeKind::Declare { local: id, value } => {
            let from = emit_node(ctx, value);
            let to = ctx.registers.create(value.type_());
            ctx.locals.get_mut(*id).value = Some(to);
            ctx.emit_move(to, from, Member::default());
            to
        }
        NodeKind::Local(id) => ctx.locals.get(*id).value.unwrap(),
        NodeKind::ConstAtEvaluation { locals, inner } => {
            let type_ = inner.type_();
            let constant =
                crate::interp::emit_and_run(ctx.thread_context, ctx.program, locals.clone(), inner);
            Value::Global(constant, type_)
        }
        NodeKind::Defer { deferred } => {
            ctx.defers.push(deferred);
            ctx.registers.zst()
        }
        NodeKind::Block { label, contents } => {
            let num_defers_at_start = ctx.defers.len();

            let to = ctx.registers.create(node.type_());

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
                emit_node(ctx, content);
            }

            let from = emit_node(ctx, contents.last().unwrap());
            ctx.emit_move(to, from, Member::default());

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
        NodeKind::Global(id, _) => ctx.program.get_constant_as_value(*id),
        NodeKind::FunctionCall {
            is_extern,
            calling: typed_calling,
            args: typed_args,
        } => {
            let to = ctx.registers.create_min_align(node.type_(), 8);
            let calling = emit_node(ctx, typed_calling);

            let mut args = vec![ctx.registers.zst(); typed_args.len()];
            for (i, arg) in typed_args {
                args[*i] = emit_node(ctx, arg);
            }

            if *is_extern {
                ctx.emit_call_extern(
                    to,
                    calling,
                    args,
                    ctx.program.ffi_calling_convention(typed_calling.type_()),
                );
            } else {
                ctx.emit_call(to, calling, args);
            }
            to
        }
    }
}

fn emit_lvalue<'a>(
    ctx: &mut Context<'a, '_>,
    can_reference_temporaries: bool,
    node: &'a Node,
) -> LValue {
    match node.kind() {
        NodeKind::Member { name, of } => {
            let parent_value = emit_lvalue(ctx, can_reference_temporaries, of);

            let member = of
                .type_()
                .member(*name)
                .expect("This should have already been made sure to exist in the typer");

            match parent_value {
                LValue::Reference(value, mut ref_member) => {
                    ref_member.name_list.push(*name);
                    ref_member.offset += member.byte_offset;
                    LValue::Reference(value, ref_member)
                }
                LValue::Value(value, mut ref_member) => {
                    ref_member.name_list.push(*name);
                    ref_member.offset += member.byte_offset;
                    LValue::Value(value, ref_member)
                }
            }
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
            operand,
        } => LValue::Reference(
            emit_node(ctx, operand),
            Member {
                offset: 0,
                name_list: Vec::new(),
            },
        ),
        NodeKind::Local(id) => LValue::Value(
            ctx.locals.get(*id).value.unwrap(),
            Member {
                offset: 0,
                name_list: Vec::new(),
            },
        ),
        NodeKind::Global(id, _) => LValue::Value(
            ctx.program.get_constant_as_value(*id),
            Member {
                offset: 0,
                name_list: Vec::new(),
            },
        ),
        kind => {
            if can_reference_temporaries {
                LValue::Value(
                    emit_node(ctx, node),
                    Member {
                        offset: 0,
                        name_list: Vec::new(),
                    },
                )
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
