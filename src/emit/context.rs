use crate::ir::{Instr, LabelId, Member, Registers, Value};
use crate::location::Location;
use crate::locals::LocalVariables;
use crate::operators::{BinaryOp, UnaryOp};
use crate::parser::ast::NodeView;
use crate::program::{FunctionId, Program, constant::ConstantRef};
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
    pub last_location: Option<Location>,

    pub defers: Vec<NodeView<'a>>,
}

impl Context<'_, '_> {
    pub fn emit_debug(&mut self, loc: Location) {
        if self.program.arguments.debug {
            if let Some(last_location) = self.last_location {
                if last_location.file == loc.file && last_location.line == loc.line {
                    return;
                }
            }

            self.instr.push(Instr::DebugLocation(loc));
        }
    }

    pub fn create_label(&mut self) -> LabelId {
        let id = LabelId(self.label_locations.len());
        self.label_locations.push(0xffff_ffff);
        id
    }

    pub fn define_label(&mut self, label_id: LabelId) {
        self.label_locations[label_id.0] = self.instr.len();
        self.instr.push(Instr::LabelDefinition(label_id));
    }

    pub fn emit_move_from_constant(&mut self, to: Value, bytes: &[u8]) {
        if to.type_().size() != 0 {
            let global = self.program.insert_buffer(to.type_(), bytes.as_ptr());
            self.instr.push(Instr::Global { to, global });
        }
    }

    pub fn emit_global(&mut self, to: Value, global: ConstantRef) {
        if to.type_().size() != 0 {
            self.instr.push(Instr::Global { to, global });
        }
    }

    pub fn emit_ref_to_global(&mut self, to: Value, global: ConstantRef, type_: crate::types::Type) {
        if type_.size() != 0 {
            println!("{}", crate::program::constant_to_str(type_, global, 0));
            self.instr.push(Instr::RefGlobal { to, global, type_ });
        }
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

    pub fn emit_truncate_int(&mut self, to: Value, from: Value, to_size: u8) {
        self.instr.push(Instr::TruncateInt { to, from, to_size });
    }

    pub fn emit_extend_int(&mut self, to: Value, from: Value, to_size: u8, from_size: u8, sign_extend: bool) {
        self.instr.push(Instr::ExtendInt { to, from, to_size, from_size, sign_extend });
    }

    pub fn emit_move_to_member_of_value(&mut self, to: Value, of: Value, member: Member) {
        if to.size() != 0 {
            self.instr.push(Instr::MoveToMemberOfValue { to, of, member });
        }
    }

    pub fn emit_member(&mut self, to: Value, of: Value, member: Member) {
        if to.size() != 0 {
            self.instr.push(Instr::Member { to, of, member });
        }
    }

    pub fn emit_pointer_to_member_of_pointer(&mut self, to: Value, of: Value, member: Member) {
        if !to.type_().is_pointer_to_zst() {
            self.instr
                .push(Instr::PointerToMemberOfPointer { to, of, member });
        }
    }

    pub fn emit_reference(&mut self, to: Value, from: Value) {
        if from.size() != 0 {
            self.instr.push(Instr::Reference { to, from });
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

    pub fn emit_bitcast(&mut self, to: Value, from: Value) {
        if to.size() != 0 {
            self.instr.push(Instr::BitCast {
                to,
                from,
            });
        }
    }

    pub fn emit_move(&mut self, to: Value, from: Value) {
        if from.size() != 0 {
            self.instr.push(Instr::Move {
                to,
                from,
            });
        }
    }

    pub fn emit_indirect_move(&mut self, to: Value, from: Value) {
        if from.size() != 0 {
            self.instr.push(Instr::MoveToPointer {
                to,
                from,
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
