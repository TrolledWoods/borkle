use super::{Instr, LabelId, Member, Registers, Routine, Value};
use crate::locals::LocalVariables;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::constant::ConstantRef;
use crate::program::thread_pool::ThreadContext;
use crate::program::Program;
use crate::typer::ast::NodeKind;
use crate::typer::Node;
use crate::types::{IntTypeKind, Type, TypeKind};

struct Context<'a> {
    thread_context: &'a mut ThreadContext,
    instr: Vec<Instr>,
    registers: Registers,
    locals: LocalVariables,
    program: &'a Program,
    label_locations: Vec<usize>,

    defers: Vec<&'a Node>,
}

impl Context<'_> {
    fn create_label(&mut self) -> LabelId {
        let id = LabelId(self.label_locations.len());
        self.label_locations.push(0xffff_ffff);
        id
    }

    fn define_label(&mut self, label_id: LabelId) {
        self.label_locations[label_id.0] = self.instr.len();
        self.instr.push(Instr::LabelDefinition(label_id));
    }

    fn emit_constant_from_constant_buffer(&mut self, to: Value, from: ConstantRef) {
        if to.size() != 0 {
            self.instr.push(Instr::Constant { to, from });
        }
    }

    fn emit_constant_from_buffer(&mut self, to: Value, buffer: &[u8]) {
        if to.size() != 0 {
            let from = self.program.insert_buffer(to.type_(), buffer.as_ptr());
            self.instr.push(Instr::Constant { to, from });
        }
    }

    /// Emits a move instruction unless the values are zero sized.
    fn emit_move(&mut self, to: Value, from: Value, member: Member) {
        if from.size() != 0 {
            self.instr.push(Instr::Move {
                to,
                from,
                size: from.size(),
                member,
            });
        }
    }

    /// Emits an indirect move instruction unless the values are zero sized.
    fn emit_move_indirect(&mut self, to: Value, from: Value, member: Member) {
        if from.size() != 0 {
            self.instr.push(Instr::MoveIndirect {
                to,
                from,
                size: from.size(),
                member,
            });
        }
    }
}

/// Emit instructions for an Ast.
pub fn emit(
    thread_context: &mut ThreadContext,
    program: &Program,
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

pub fn emit_function_declaration(
    thread_context: &mut ThreadContext,
    program: &Program,
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
            is_extern: _,
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
        .insert_buffer(type_, unsafe { *id.to_le_bytes().as_ptr().cast() })
}

fn emit_node<'a>(ctx: &mut Context<'a>, node: &'a Node) -> Value {
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
            ctx.instr.push(Instr::Jump { to: ir_label });

            ctx.registers.zst()
        }
        NodeKind::While { condition, body } => {
            let end_label = ctx.create_label();

            let condition_label = ctx.create_label();
            ctx.define_label(condition_label);
            let condition = emit_node(ctx, condition);

            ctx.instr.push(Instr::JumpIfZero {
                condition,
                to: end_label,
            });

            emit_node(ctx, body);

            ctx.instr.push(Instr::Jump {
                to: condition_label,
            });

            ctx.define_label(end_label);

            ctx.registers.zst()
        }
        NodeKind::If {
            condition,
            true_body,
            false_body: None,
        } => {
            let condition = emit_node(ctx, condition);

            let end_of_body = ctx.create_label();
            ctx.instr.push(Instr::JumpIfZero {
                condition,
                to: end_of_body,
            });

            emit_node(ctx, true_body);

            ctx.define_label(end_of_body);

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

            ctx.instr.push(Instr::JumpIfZero {
                condition,
                to: start_of_false_body,
            });

            let to = ctx.registers.create(node.type_());

            // True body
            let true_body = emit_node(ctx, true_body);
            ctx.emit_move(to, true_body, Member::default());
            ctx.instr.push(Instr::Jump {
                to: end_of_false_body,
            });

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
        NodeKind::FunctionDeclaration { locals, body } => {
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
            ctx.instr.push(Instr::Member {
                to,
                of,
                member: Member {
                    offset: of.type_().member(*name).unwrap().byte_offset,
                    name_list: vec![*name],
                },
            });
            to
        }
        NodeKind::Binary { op, left, right } => {
            let to = ctx.registers.create(node.type_());

            let a = emit_node(ctx, left);
            let b = emit_node(ctx, right);

            ctx.instr.push(Instr::Binary {
                op: *op,
                to,
                a,
                b,
                left_type: left.type_(),
                right_type: right.type_(),
            });

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
            ctx.instr.push(Instr::Reference {
                to: reference,
                from: to,
                offset: Member::default(),
            });
            let one = ctx
                .registers
                .create(Type::new(TypeKind::Int(IntTypeKind::Usize)));
            ctx.emit_constant_from_buffer(one, &1_usize.to_le_bytes());
            for (i, element) in elements.iter().enumerate() {
                if i > 0 {
                    ctx.instr.push(Instr::Binary {
                        op: BinaryOp::Add,
                        to: reference,
                        a: reference,
                        b: one,
                        left_type: ref_type,
                        right_type: Type::new(TypeKind::Int(IntTypeKind::Usize)),
                    });
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
                    ctx.instr.push(Instr::Member {
                        to,
                        of: from,
                        member,
                    });
                }
                LValue::Value(from, offset) => {
                    ctx.instr.push(Instr::Reference { to, from, offset });
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
            ctx.instr.push(Instr::Dereference { to, from });
            to
        }
        NodeKind::Unary { op, operand } => {
            let to = ctx.registers.create(node.type_());
            let from = emit_node(ctx, operand);
            ctx.instr.push(Instr::Unary { op: *op, to, from });
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
        NodeKind::Global(id) => ctx.program.get_constant_as_value(*id),
        NodeKind::FunctionCall {
            is_extern,
            calling: typed_calling,
            args: typed_args,
        } => {
            let to = ctx.registers.create_min_align(node.type_(), 8);
            let calling = emit_node(ctx, typed_calling);

            let mut args = Vec::with_capacity(typed_args.len());
            for arg in typed_args {
                args.push(emit_node(ctx, arg));
            }

            if *is_extern {
                ctx.instr.push(Instr::CallExtern {
                    to,
                    pointer: calling,
                    args,
                    convention: ctx.program.ffi_calling_convention(typed_calling.type_()),
                });
            } else {
                ctx.instr.push(Instr::Call {
                    to,
                    pointer: calling,
                    args,
                });
            }
            to
        }
    }
}

fn emit_lvalue<'a>(
    ctx: &mut Context<'a>,
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
        NodeKind::Global(id) => LValue::Value(
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
