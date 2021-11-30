use crate::ir::{Instr, LabelId, Member, Registers, Value};
use crate::location::Location;
use crate::locals::LocalVariables;
use crate::operators::{BinaryOp, UnaryOp};
use crate::parser::ast::{Ast, NodeId};
use crate::program::{FunctionId, Program};
use crate::thread_pool::ThreadContext;
use crate::type_infer::TypeSystem;

pub struct Context<'a, 'b> {
    pub thread_context: &'a mut ThreadContext<'b>,
    pub instr: Vec<Instr>,
    pub registers: Registers,
    pub locals: &'a mut LocalVariables,
    pub program: &'b Program,
    pub types: &'a mut TypeSystem,
    pub label_locations: Vec<usize>,
    pub calling: Vec<FunctionId>,
    pub ast: &'a Ast,

    pub defers: Vec<NodeId>,
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

    pub fn emit_set_to_zero(&mut self, to: Value) {
        let size = to.type_().size();
        self.instr.push(Instr::SetToZero { to, size });
    }

    pub fn emit_member(&mut self, to: Value, of: Value, member: Member) {
        if to.size() != 0 {
            self.instr.push(Instr::Member { to, of, member });
        }
    }

    pub fn emit_pointer_to_member_of_pointer(&mut self, to: Value, of: Value, member: Member) {
        debug_assert_eq!(
            to.size(),
            8,
            "When emitting an indirect member the 'to' value has to be a pointer"
        );
        if !to.type_().is_pointer_to_zst() {
            self.instr
                .push(Instr::PointerToMemberOfPointer { to, of, member });
        }
    }

    pub fn emit_pointer_to_member_of_value(&mut self, to: Value, from: Value, offset: Member) {
        if from.type_().size() != 0 {
            self.instr
                .push(Instr::PointerToMemberOfValue { to, from, offset });
        }
    }

    pub fn emit_dereference(&mut self, to: Value, from: Value) {
        if to.size() != 0 {
            self.instr.push(Instr::Dereference { to, from });
        }
    }

    pub fn emit_increment(&mut self, value: Value) {
        if value.size() != 0 {
            self.instr.push(Instr::Increment { value });
        }
    }

    pub fn emit_move_from_constant(&mut self, to: Value, from: &[u8]) {
        if to.size() != 0 {
            let buffer = self.program.insert_buffer(to.type_(), from.as_ptr());
            self.emit_move(to, Value::Global(buffer, to.type_()));
        }
    }

    pub fn emit_move(&mut self, to: Value, from: Value) {
        self.emit_move_to_member_of_value(to, from, Member::default())
    }

    pub fn emit_indirect_move(&mut self, to: Value, from: Value) {
        self.emit_move_to_member_of_pointer(to, from, Member::default())
    }

    /// Emits a move instruction unless the values are zero sized.
    pub fn emit_move_to_member_of_value(&mut self, to: Value, from: Value, member: Member) {
        if from.size() != 0 {
            self.instr.push(Instr::MoveToMemberOfValue {
                to,
                from,
                size: from.size(),
                member,
            });
        }
    }

    /// Emits an indirect move instruction unless the values are zero sized.
    pub fn emit_move_to_member_of_pointer(&mut self, to: Value, from: Value, member: Member) {
        if from.size() != 0 {
            self.instr.push(Instr::MoveToMemberOfPointer {
                to,
                from,
                size: from.size(),
                member,
            });
        }
    }

    pub fn emit_call(&mut self, to: Value, pointer: Value, args: Vec<Value>, loc: Location) {
        self.instr.push(Instr::Call { to, pointer, args, loc });
    }

    pub fn emit_unary(&mut self, op: UnaryOp, to: Value, from: Value) {
        if to.size() != 0 {
            self.instr.push(Instr::Unary { op, to, from });
        }
    }

    pub fn emit_binary(&mut self, op: BinaryOp, to: Value, a: Value, b: Value) {
        if to.size() != 0 {
            self.instr.push(Instr::Binary { op, to, a, b });
        }
    }
}
