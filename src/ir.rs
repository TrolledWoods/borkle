use crate::operators::{BinaryOp, UnaryOp};
use crate::types::{to_align, Type};
use ustr::Ustr;

pub mod emit;

#[derive(Debug, Clone)]
pub enum Instr {
    Constant {
        to: Value,
        from: Vec<u8>,
    },
    Binary {
        op: BinaryOp,
        to: Value,
        a: Value,
        b: Value,
    },
    Unary {
        op: UnaryOp,
        to: Value,
        from: Value,
    },
    Member {
        to: Value,
        of: Value,
        name: Ustr,
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
        size: usize,
    },
    /// Move 'from' into the memory location pointed to by
    /// 'to'.
    MoveIndirect {
        to: Value,
        from: Value,
        size: usize,
    },
}

pub struct Routine {
    pub instr: Vec<Instr>,
    pub registers: Registers,
    pub result: Value,
}

pub struct Registers {
    locals: Vec<Register>,
    // If you had a buffer with a bunch of locals inside,
    // how big would that buffer have to be to fit all of them?
    buffer_size: usize,
}

impl Registers {
    fn new() -> Self {
        Self {
            locals: Vec::new(),
            buffer_size: 0,
        }
    }

    fn create(&mut self, type_: impl Into<Type>) -> Value {
        let type_ = type_.into();
        self.buffer_size = to_align(self.buffer_size, type_.align());
        let value = Value(self.locals.len());
        self.locals.push(Register {
            offset: self.buffer_size,
            type_,
        });
        self.buffer_size += type_.size();
        value
    }
}

struct Register {
    offset: usize,
    type_: Type,
}

#[derive(Debug, Clone, Copy)]
pub struct Value(usize);
