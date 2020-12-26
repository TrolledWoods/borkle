use crate::operators::{BinaryOp, UnaryOp};
use crate::program::constant::ConstantRef;
use crate::program::ffi;
use crate::types::{to_align, Type, TypeKind};
use ustr::Ustr;

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
        from: ConstantRef,
    },
    Increment {
        value: Value,
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
        member: Member,
    },
    Dereference {
        to: Value,
        from: Value,
    },
    Reference {
        to: Value,
        from: Value,
        offset: Member,
    },
    Move {
        to: Value,
        from: Value,
        size: usize,
        member: Member,
    },
    MoveIndirect {
        to: Value,
        from: Value,
        size: usize,
        member: Member,
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

#[derive(Default, Debug, Clone)]
pub struct Member {
    pub offset: usize,
    // FIXME: This is inefficient af!!!!
    pub name_list: Vec<Ustr>,
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
    max_buffer_size: usize,
    buffer_head: usize,
}

impl Registers {
    pub fn new() -> Self {
        Self {
            locals: Vec::new(),
            max_buffer_size: 0,
            buffer_head: 0,
        }
    }

    pub fn buffer_size(&self) -> usize {
        self.max_buffer_size.max(self.buffer_head)
    }

    pub fn get_head(&self) -> usize {
        self.buffer_head
    }

    pub fn set_head(&mut self, head: usize) {
        assert!(head <= self.buffer_head);

        self.max_buffer_size = self.max_buffer_size.max(self.buffer_head);
        self.buffer_head = head;
    }

    pub fn create(&mut self, type_: impl Into<Type>) -> Value {
        self.create_min_align(type_.into(), 1)
    }

    pub fn zst(&mut self) -> Value {
        self.create(TypeKind::Empty)
    }

    pub fn create_min_align(&mut self, type_: impl Into<Type>, min_align: usize) -> Value {
        let type_ = type_.into();
        let mut align = type_.align();
        if align < min_align {
            align = min_align;
        }
        self.buffer_head = to_align(self.buffer_head, align);
        let value = Value::Register(self.locals.len(), type_);
        self.locals.push(Register {
            offset: self.buffer_head,
            type_,
        });
        self.buffer_head += to_align(type_.size(), align);
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
    Global(ConstantRef, Type),
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

    pub fn size(&self) -> usize {
        self.type_().size()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LabelId(pub usize);
