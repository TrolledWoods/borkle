use crate::operators::{BinaryOp, UnaryOp};
use crate::program::ffi;
use crate::types::{to_align, Type, TypeKind};
use std::ptr::NonNull;
use ustr::Ustr;

pub mod emit;

#[derive(Debug, Clone)]
pub enum Instr {
    CallExtern {
        to: Value,
        pointer: Value,
        // FIXME: We don't really want a vector here, we want a more efficient datastructure
        args: Vec<Value>,
        convention: ffi::CallingConvention,
    },
    Call {
        to: Value,
        pointer: Value,
        // FIXME: We don't really want a vector here, we want a more efficient datastructure
        args: Vec<Value>,
    },
    Constant {
        to: Value,
        from: Vec<u8>,
    },
    Binary {
        op: BinaryOp,
        to: Value,
        a: Value,
        b: Value,
        type_: Type,
    },
    Unary {
        op: UnaryOp,
        to: Value,
        from: Value,
    },
    Member {
        to: Value,
        of: Value,
        offset: usize,
        name: Ustr,
        size: usize,
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
        // FIXME: rename to 'target' maybe?
        to: Value,
        from: Value,
        size: usize,
        offset_to_target: usize,
    },
    MoveIndirect {
        // FIXME: rename to 'target' maybe?
        to: Value,
        from: Value,
        size: usize,
        offset_to_target: usize,
    },
    JumpIfZero {
        condition: Value,
        to: LabelId,
    },
    Jump {
        to: LabelId,
    },
    LabelDefinition(LabelId),
}

// Why is this safe? Well, because we do not have interior mutability anywhere, so the raw pointers
// are okay.
unsafe impl Send for Instr {}
unsafe impl Sync for Instr {}

pub struct Routine {
    pub label_locations: Vec<usize>,
    pub instr: Vec<Instr>,
    pub registers: Registers,
    pub result: Value,
}

pub struct Registers {
    pub(crate) locals: Vec<Register>,
    // If you had a buffer with a bunch of locals inside,
    // how big would that buffer have to be to fit all of them?
    pub(crate) buffer_size: usize,
}

impl Registers {
    fn new() -> Self {
        Self {
            locals: Vec::new(),
            buffer_size: 0,
        }
    }

    fn create(&mut self, type_: impl Into<Type>) -> Value {
        self.create_min_align(type_.into(), 1)
    }

    fn zst(&mut self) -> Value {
        self.create(TypeKind::Empty)
    }

    fn create_min_align(&mut self, type_: impl Into<Type>, min_align: usize) -> Value {
        let type_ = type_.into();
        let mut align = type_.align();
        if align < min_align {
            align = min_align;
        }
        self.buffer_size = to_align(self.buffer_size, align);
        let value = Value::Register(self.locals.len(), type_);
        self.locals.push(Register {
            offset: self.buffer_size,
            type_,
        });
        self.buffer_size += to_align(type_.size(), align);
        value
    }

    pub(crate) fn get(&self, index: usize) -> &'_ Register {
        &self.locals[index]
    }
}

pub(crate) struct Register {
    offset: usize,
    pub(crate) type_: Type,
}

impl Register {
    pub(crate) fn offset(&self) -> usize {
        self.offset
    }

    pub(crate) fn size(&self) -> usize {
        self.type_.size()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Value {
    Register(usize, Type),
    Global(NonNull<u8>, Type),
}

unsafe impl Send for Value {}
unsafe impl Sync for Value {}

impl Value {
    pub fn type_(&self) -> Type {
        match self {
            Self::Register(_, type_) => *type_,
            Self::Global(_, type_) => *type_,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LabelId(pub usize);
