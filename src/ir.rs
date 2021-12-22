use crate::operators::{BinaryOp, UnaryOp};
use crate::location::Location;
use crate::program::{constant::ConstantRef, BuiltinFunction};
use crate::types::{to_align, Type, TypeKind};
use crate::type_infer::{TypeSystem, ValueId as TypeId, self};
use std::fmt;

#[derive(Clone, Debug)]
#[allow(non_camel_case_types)]
pub enum Instr {
    // to = pointer(args)
    Call {
        to: Value,
        pointer: Value,
        // FIXME: We don't really want a vector here, we want a more efficient datastructure
        args: Vec<Value>,
        loc: Location,
    },
    SetToZero {
        to: Value,
        size: usize,
    },
    // value ++
    Increment {
        value: Value,
    },
    // to = a op b
    Binary {
        op: BinaryOp,
        to: Value,
        a: Value,
        b: Value,
    },
    // to = op from
    Unary {
        op: UnaryOp,
        to: Value,
        from: Value,
    },
    // to = of.member
    Member {
        to: Value,
        of: Value,
        member: Member,
    },
    // to = *from
    Dereference {
        to: Value,
        from: Value,
    },
    TruncateInt {
        to: Value,
        from: Value,
        to_size: u8,
    },
    ExtendInt {
        to: Value,
        from: Value,
        from_size: u8,
        to_size: u8,
        sign_extend: bool,
    },
    BitCast {
        to: Value,
        from: Value,
    },
    // to = &from.offset
    PointerToMemberOfValue {
        to: Value,
        from: Value,
        offset: Member,
    },
    // to = &(*of).member
    PointerToMemberOfPointer {
        to: Value,
        of: Value,
        member: Member,
    },
    // to.member = from
    MoveToMemberOfValue {
        to: Value,
        from: Value,
        size: usize,
        member: Member,
    },
    // (*to).member = from
    MoveToMemberOfPointer {
        to: Value,
        from: Value,
        size: usize,
        member: Member,
    },
    // jump to 'to' if condition
    JumpIfZero {
        condition: Value,
        to: LabelId,
    },
    // jump to 'to'
    Jump {
        to: LabelId,
    },
    LabelDefinition(LabelId),
}

#[derive(Default, Debug, Clone, Copy)]
pub struct Member {
    pub offset: usize,
    pub amount: usize,
}

// Why is this safe? Well, because we do not have interior mutability anywhere, so the raw pointers
// are okay.
unsafe impl Send for Instr {}
unsafe impl Sync for Instr {}

pub enum Routine {
    Builtin(BuiltinFunction),
    UserDefined(UserDefinedRoutine),
}

pub struct UserDefinedRoutine {
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

    pub fn create(&mut self, _types: &TypeSystem, _value: TypeId, type_: impl Into<Type>) -> Value {
        self.create_min_align(type_.into(), 1)
    }

    pub fn zst(&mut self) -> Value {
        self.create_min_align(TypeKind::Empty, 1)
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

impl fmt::Display for Value {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Register(id, type_) => write!(fmt, "{} {}", type_, id),
            Value::Global(_, type_) => write!(fmt, "const {}", type_),
        }
    }
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
