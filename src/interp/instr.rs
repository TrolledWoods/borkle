use crate::operators::{BinaryOp, UnaryOp};
use crate::program::constant::ConstantRef;
use crate::program::ffi;
use crate::types::Type;
use crate::location::Location;

pub enum Instr {
    DebugLocation(Location, String),
    CallExtern {
        to: Value,
        pointer: Value,
        args: Vec<Value>,
        convention: ffi::CallingConvention,
    },
    Call {
        to: Value,
        pointer: Value,
        args: Vec<Value>,
    },
    Constant {
        to: Value,
        from: ConstantRef,
    },
    Increment {
        value: Value,
        amount: usize,
    },
    Binary {
        op: BinaryOp,
        to: Value,
        left: Value,
        right: Value,
        left_type: Type,
        right_type: Type,
    },
    Unary {
        op: UnaryOp,
        to: Value,
        operand: Value,
    },
    Member {
        to: Value,
        of: Value,
        member: usize,
    },
    Dereference {
        to: Value,
        from: Value,
    },
    Reference {
        to: Value,
        from: Value,
    },
    Move {
        to: Value,
        from: Value,
        to_offset: usize,
    },
    MoveIndirect {
        to: Value,
        from: Value,
        to_offset: usize,
    },
    JumpIfZero {
        condition: Value,
        to: usize,
    },
    Jump {
        to: usize,
    },
}

#[derive(Clone, Copy)]
pub enum Value {
    Register { offset: usize, size: usize },
    Global { ptr: ConstantRef, size: usize },
}
