use super::{Instr, LabelId, Member, Registers, Routine, Value};
use crate::locals::LocalVariables;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::constant::ConstantRef;
use crate::program::thread_pool::ThreadContext;
use crate::program::Program;
use crate::typer::ast::NodeKind;
use crate::typer::Ast;
use crate::types::{IntTypeKind, Type, TypeKind};

type Node<'a> = bump_tree::Node<'a, crate::typer::ast::Node>;

struct Context<'a> {
    thread_context: &'a mut ThreadContext,
    instr: Vec<Instr>,
    registers: Registers,
    locals: LocalVariables,
    program: &'a Program,
    label_locations: Vec<usize>,

    defers: Vec<Node<'a>>,
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
    ast: &Ast,
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

    let result = emit_node(&mut ctx, ast.root().unwrap());

    Routine {
        instr: ctx.instr,
        registers: ctx.registers,
        result,
        label_locations: ctx.label_locations,
    }
}

fn emit_node<'a>(ctx: &mut Context<'a>, node: Node<'a>) -> Value {
    match node.to_ref().kind() {
        NodeKind::Break(label_id, num_deduplicated_defers_at_target) => {
            let label = ctx.locals.get_label(*label_id);
            let ir_label = label.ir_labels.as_ref().unwrap()[*num_deduplicated_defers_at_target];
            let value = label.value.unwrap();

            let from = emit_node(ctx, node.children().next().unwrap());

            let label = ctx.locals.get_label(*label_id);
            for defer_index in
                (label.defer_depth + *num_deduplicated_defers_at_target..ctx.defers.len()).rev()
            {
                emit_node(ctx, ctx.defers[defer_index]);
            }

            ctx.emit_move(value, from, Member::default());
            ctx.instr.push(Instr::Jump { to: ir_label });

            ctx.registers.zst()
        }
        NodeKind::While => {
            let mut children = node.children();

            let end_label = ctx.create_label();

            let condition_label = ctx.create_label();
            ctx.define_label(condition_label);
            let condition = emit_node(ctx, children.next().unwrap());

            ctx.instr.push(Instr::JumpIfZero {
                condition,
                to: end_label,
            });

            emit_node(ctx, children.next().unwrap());

            ctx.instr.push(Instr::Jump {
                to: condition_label,
            });

            ctx.define_label(end_label);

            ctx.registers.zst()
        }
        NodeKind::If { has_else: false } => {
            let mut children = node.children();
            let condition = emit_node(ctx, children.next().unwrap());

            let end_of_body = ctx.create_label();
            ctx.instr.push(Instr::JumpIfZero {
                condition,
                to: end_of_body,
            });

            // Emit the body
            emit_node(ctx, children.next().unwrap());

            ctx.define_label(end_of_body);

            ctx.registers.zst()
        }
        NodeKind::If { has_else: true } => {
            let mut children = node.children();
            let condition = emit_node(ctx, children.next().unwrap());

            let start_of_false_body = ctx.create_label();
            let end_of_false_body = ctx.create_label();

            ctx.instr.push(Instr::JumpIfZero {
                condition,
                to: start_of_false_body,
            });

            let to = ctx.registers.create(node.type_());

            // True body
            let true_body = emit_node(ctx, children.next().unwrap());
            ctx.emit_move(to, true_body, Member::default());
            ctx.instr.push(Instr::Jump {
                to: end_of_false_body,
            });

            // False body
            ctx.define_label(start_of_false_body);
            let false_body = emit_node(ctx, children.next().unwrap());
            ctx.emit_move(to, false_body, Member::default());

            ctx.define_label(end_of_false_body);

            to
        }
        NodeKind::Uninit => {
            // We don't need an instruction to initialize the memory, because it's uninit!
            ctx.registers.create(node.type_())
        }
        NodeKind::FunctionDeclaration { locals } => {
            let mut sub_ctx = Context {
                thread_context: ctx.thread_context,
                instr: Vec::new(),
                registers: Registers::new(),
                locals: locals.clone(),
                program: ctx.program,
                label_locations: Vec::new(),
                defers: Vec::new(),
            };

            // Allocate registers for all the locals
            for local in sub_ctx.locals.iter_mut() {
                let value = sub_ctx.registers.create(local.type_.unwrap());
                local.value = Some(value);
            }

            let result = emit_node(&mut sub_ctx, node.children().next().unwrap());
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
                } = node.type_().kind()
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

            let to = ctx.registers.create(node.type_());
            ctx.emit_constant_from_buffer(to, &id.to_le_bytes());
            to
        }
        NodeKind::BitCast => {
            let from = emit_node(ctx, node.children().next().unwrap());
            let to = ctx.registers.create(node.type_());
            ctx.emit_move(to, from, Member::default());
            to
        }
        NodeKind::ArrayToBuffer(len) => {
            let from = emit_node(ctx, node.children().next().unwrap());
            let to = ctx.registers.create(node.type_());

            let len_reg = ctx
                .registers
                .create(Type::new(TypeKind::Int(IntTypeKind::Usize)));
            ctx.emit_constant_from_buffer(len_reg, &len.to_le_bytes());

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
        NodeKind::Member(name) => {
            let to = ctx.registers.create(node.type_());
            let of_node = node.children().next().unwrap();
            let of = emit_node(ctx, of_node);
            ctx.instr.push(Instr::Member {
                to,
                of,
                member: Member {
                    offset: of_node.type_().member(*name).unwrap().byte_offset,
                    name_list: vec![*name],
                },
            });
            to
        }
        NodeKind::Binary(op) => {
            let to = ctx.registers.create(node.type_());

            let mut children = node.children();
            let left_node = children.next().unwrap();
            let right_node = children.next().unwrap();

            let a = emit_node(ctx, left_node);
            let b = emit_node(ctx, right_node);

            ctx.instr.push(Instr::Binary {
                op: *op,
                to,
                a,
                b,
                left_type: left_node.type_(),
                right_type: right_node.type_(),
            });

            to
        }
        NodeKind::ArrayLiteral(_) => {
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
            for (i, child) in node.children().enumerate() {
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
                let from = emit_node(ctx, child);
                ctx.emit_move_indirect(reference, from, Member::default());
            }
            to
        }
        NodeKind::Unary(UnaryOp::Reference) => {
            let to = ctx.registers.create(node.type_());
            let from = emit_lvalue(ctx, true, node.children().next().unwrap());
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
        NodeKind::Unary(UnaryOp::Dereference) => {
            let to = ctx.registers.create(node.type_());
            let from = emit_node(ctx, node.children().next().unwrap());
            ctx.instr.push(Instr::Dereference { to, from });
            to
        }
        NodeKind::Unary(op) => {
            let to = ctx.registers.create(node.type_());
            let from = emit_node(ctx, node.children().next().unwrap());
            ctx.instr.push(Instr::Unary { op: *op, to, from });
            to
        }
        NodeKind::Assign => {
            let mut children = node.children();

            let to = emit_lvalue(ctx, false, children.next().unwrap());

            let from_node = children.next().unwrap();
            let from = emit_node(ctx, from_node);

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
        NodeKind::Declare(id) => {
            let mut children = node.children();
            let child = children.next().unwrap();
            let from = emit_node(ctx, child);
            let to = ctx.registers.create(child.type_());
            ctx.locals.get_mut(*id).value = Some(to);
            ctx.emit_move(to, from, Member::default());
            to
        }
        NodeKind::Local(id) => ctx.locals.get(*id).value.unwrap(),
        NodeKind::Defer(ref ast) => {
            ctx.defers.push(ast.root().unwrap());
            ctx.registers.zst()
        }
        NodeKind::Block { label } => {
            let num_defers_at_start = ctx.defers.len();

            let to = ctx.registers.create(node.type_());

            if let Some(label) = *label {
                let ir_labels = (0..ctx.locals.get_label(label).num_defers + 1)
                    .map(|_| ctx.create_label())
                    .collect();
                let label_ref = ctx.locals.get_label_mut(label);
                label_ref.ir_labels = Some(ir_labels);
                label_ref.value = Some(to);
            }

            let mut children = node.children();
            let len = children.len();
            let head = ctx.registers.get_head();

            for child in children.by_ref().take(len - 1) {
                emit_node(ctx, child);
            }

            let from = emit_node(ctx, children.next().unwrap());
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
        NodeKind::FunctionCall { is_extern } => {
            let to = ctx.registers.create_min_align(node.type_(), 8);
            let mut children = node.children();
            let pointer_node = children.next().unwrap();
            let pointer = emit_node(ctx, pointer_node);

            let mut args = Vec::with_capacity(children.len());
            for child in children {
                args.push(emit_node(ctx, child));
            }

            if *is_extern {
                ctx.instr.push(Instr::CallExtern {
                    to,
                    pointer,
                    args,
                    convention: ctx.program.ffi_calling_convention(pointer_node.type_()),
                });
            } else {
                ctx.instr.push(Instr::Call { to, pointer, args });
            }
            to
        }
    }
}

fn emit_lvalue<'a>(
    ctx: &mut Context<'a>,
    can_reference_temporaries: bool,
    node: Node<'a>,
) -> LValue {
    match node.kind() {
        NodeKind::Member(name) => {
            let mut children = node.children();
            let parent_node = children.next().unwrap();
            let parent_value = emit_lvalue(ctx, can_reference_temporaries, parent_node);

            let member = parent_node
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
        NodeKind::Unary(UnaryOp::Dereference) => {
            let mut children = node.children();
            let pointee = children.next().unwrap();
            LValue::Reference(
                emit_node(ctx, pointee),
                Member {
                    offset: 0,
                    name_list: Vec::new(),
                },
            )
        }
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
