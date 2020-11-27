use super::{Instr, Registers, Routine, Value};
use crate::locals::LocalVariables;
use crate::operators::UnaryOp;
use crate::program::Program;
use crate::typer::ast::NodeKind;
use crate::typer::Ast;

type Node<'a> = bump_tree::Node<'a, crate::typer::ast::Node>;

struct Context<'a> {
    instr: Vec<Instr>,
    registers: Registers,
    locals: LocalVariables,
    program: &'a Program,
}

/// Emit instructions for an Ast.
pub fn emit(program: &Program, locals: LocalVariables, ast: &Ast) -> Routine {
    let mut ctx = Context {
        instr: Vec::new(),
        registers: Registers::new(),
        locals,
        program,
    };

    // Allocate registers for all the locals
    for local in ctx.locals.iter_mut() {
        let value = ctx.registers.create(local.type_.unwrap());
        local.value = Some(value);
    }

    let result = emit_node(&mut ctx, &ast.root().unwrap());

    Routine {
        instr: ctx.instr,
        registers: ctx.registers,
        result,
    }
}

fn emit_node(ctx: &mut Context<'_>, node: &Node<'_>) -> Value {
    match node.kind() {
        NodeKind::FunctionDeclaration { locals } => {
            let mut sub_ctx = Context {
                instr: Vec::new(),
                registers: Registers::new(),
                locals: locals.clone(),
                program: ctx.program,
            };

            // Allocate registers for all the locals
            for local in sub_ctx.locals.iter_mut() {
                let value = sub_ctx.registers.create(local.type_.unwrap());
                local.value = Some(value);
            }

            let result = emit_node(&mut sub_ctx, &node.children().next().unwrap());

            let id = sub_ctx.program.insert_function(Routine {
                instr: sub_ctx.instr,
                registers: sub_ctx.registers,
                result,
            });

            let to = ctx.registers.create(node.type_());
            ctx.instr.push(Instr::Constant {
                to,
                from: id.to_le_bytes().into(),
            });
            to
        }
        NodeKind::BitCast => {
            let from = emit_node(ctx, &node.children().next().unwrap());
            let to = ctx.registers.create(node.type_());
            ctx.instr.push(Instr::Move {
                to,
                from,
                size: node.type_().size(),
            });
            to
        }
        NodeKind::Constant(bytes) => {
            let to = ctx.registers.create(node.type_());
            ctx.instr.push(Instr::Constant {
                to,
                from: bytes.0.clone(),
            });
            to
        }
        NodeKind::Member(name) => {
            let to = ctx.registers.create(node.type_());
            let of = emit_node(ctx, &node.children().next().unwrap());
            ctx.instr.push(Instr::Member {
                to,
                of,
                name: *name,
            });
            to
        }
        NodeKind::Binary(op) => {
            let to = ctx.registers.create(node.type_());
            let mut children = node.children();
            let a = emit_node(ctx, &children.next().unwrap());
            let b = emit_node(ctx, &children.next().unwrap());
            ctx.instr.push(Instr::Binary {
                op: *op,
                to,
                a,
                b,
                type_: node.type_(),
            });
            to
        }
        NodeKind::Unary(UnaryOp::Reference) => {
            let to = ctx.registers.create(node.type_());
            let from = emit_node(ctx, &node.children().next().unwrap());
            ctx.instr.push(Instr::Reference { to, from });
            to
        }
        NodeKind::Unary(UnaryOp::Dereference) => {
            let to = ctx.registers.create(node.type_());
            let from = emit_node(ctx, &node.children().next().unwrap());
            ctx.instr.push(Instr::Dereference { to, from });
            to
        }
        NodeKind::Unary(op) => {
            let to = ctx.registers.create(node.type_());
            let from = emit_node(ctx, &node.children().next().unwrap());
            ctx.instr.push(Instr::Unary { op: *op, to, from });
            to
        }
        NodeKind::Assign(local_id) => {
            let to = ctx.registers.create(node.type_());
            let from_node = node.children().next().unwrap();
            let from = emit_node(ctx, &from_node);
            ctx.instr.push(Instr::Move {
                to: ctx.locals.get(*local_id).value.unwrap(),
                from,
                size: from_node.type_().size(),
            });
            to
        }
        NodeKind::Local(id) => ctx.locals.get(*id).value.unwrap(),
        NodeKind::Block => {
            let mut children = node.children();
            let len = children.len();
            for child in children.by_ref().take(len - 1) {
                emit_node(ctx, &child);
            }
            emit_node(ctx, &children.next().unwrap())
        }
        NodeKind::Global(id) => {
            let to = ctx.registers.create(node.type_());
            ctx.instr.push(Instr::Global { to, from: *id });
            to
        }
        NodeKind::FunctionCall { is_extern } => {
            let to = ctx.registers.create_min_align(node.type_(), 8);
            let mut children = node.children();
            let pointer_node = children.next().unwrap();
            let pointer = emit_node(ctx, &pointer_node);

            let mut args = Vec::with_capacity(children.len());
            for child in children {
                args.push(emit_node(ctx, &child));
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
