use crate::ir::{Instr, LabelId, Member, Registers, Value};
use crate::locals::LocalVariables;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::constant::ConstantRef;
use crate::program::thread_pool::ThreadContext;
use crate::program::Program;
use crate::typer::ast::Node;
use crate::types::Type;

pub struct Context<'a, 'b> {
    pub thread_context: &'a mut ThreadContext<'b>,
    pub instr: Vec<Instr>,
    pub registers: Registers,
    pub locals: LocalVariables,
    pub program: &'b Program,
    pub label_locations: Vec<usize>,

    pub defers: Vec<&'a Node>,
}

impl Context<'_, '_> {
    pub fn create_label(&mut self) -> LabelId {
        let id = LabelId(self.label_locations.len());
        self.label_locations.push(0xffff_ffff);
        id
    }

    pub fn define_label(&mut self, label_id: LabelId) {
        self.label_locations[label_id.0] = self.instr.len();
        self.instr.push(Instr::LabelDefinition(label_id));
    }

    pub fn emit_jump_if_zero(&mut self, condition: Value, to: LabelId) {
        self.instr.push(Instr::JumpIfZero { condition, to });
    }

    pub fn emit_jump(&mut self, to: LabelId) {
        self.instr.push(Instr::Jump { to });
    }

    pub fn emit_member(&mut self, to: Value, of: Value, member: Member) {
        if to.size() != 0 {
            self.instr.push(Instr::Member { to, of, member });
        }
    }

    pub fn emit_reference(&mut self, to: Value, from: Value, offset: Member) {
        if from.size() != 0 {
            self.instr.push(Instr::Reference { to, from, offset });
        }
    }

    pub fn emit_dereference(&mut self, to: Value, from: Value) {
        if to.size() != 0 {
            self.instr.push(Instr::Dereference { to, from });
        }
    }

    pub fn emit_constant_from_constant_buffer(&mut self, to: Value, from: ConstantRef) {
        if to.size() != 0 {
            self.instr.push(Instr::Constant { to, from });
        }
    }

    pub fn emit_constant_from_buffer(&mut self, to: Value, buffer: &[u8]) {
        if to.size() != 0 {
            let from = self.program.insert_buffer(to.type_(), buffer.as_ptr());
            self.instr.push(Instr::Constant { to, from });
        }
    }

    pub fn emit_increment(&mut self, value: Value) {
        if value.size() != 0 {
            self.instr.push(Instr::Increment { value });
        }
    }

    /// Emits a move instruction unless the values are zero sized.
    pub fn emit_move(&mut self, to: Value, from: Value, member: Member) {
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
    pub fn emit_move_indirect(&mut self, to: Value, from: Value, member: Member) {
        if from.size() != 0 {
            self.instr.push(Instr::MoveIndirect {
                to,
                from,
                size: from.size(),
                member,
            });
        }
    }

    pub fn emit_call_extern(
        &mut self,
        to: Value,
        pointer: Value,
        args: Vec<Value>,
        convention: crate::program::ffi::CallingConvention,
    ) {
        self.instr.push(Instr::CallExtern {
            to,
            pointer,
            args,
            convention,
        });
    }

    pub fn emit_call(&mut self, to: Value, pointer: Value, args: Vec<Value>) {
        self.instr.push(Instr::Call { to, pointer, args });
    }

    pub fn emit_unary(&mut self, op: UnaryOp, to: Value, from: Value) {
        if to.size() != 0 {
            self.instr.push(Instr::Unary { op, to, from });
        }
    }

    pub fn emit_binary(
        &mut self,
        op: BinaryOp,
        to: Value,
        a: Value,
        b: Value,
        left_type: Type,
        right_type: Type,
    ) {
        if to.size() != 0 {
            self.instr.push(Instr::Binary {
                op,
                to,
                a,
                b,
                left_type,
                right_type,
            });
        }
    }
}
