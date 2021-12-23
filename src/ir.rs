use crate::operators::{BinaryOp, UnaryOp};
use crate::location::Location;
use crate::program::{constant::ConstantRef, BuiltinFunction};
use crate::types::{to_align, Type, TypeKind};
use crate::type_infer::{TypeSystem, ValueId as TypeId, self};
use ustr::Ustr;
use std::fmt;

#[derive(Clone, Debug)]
#[allow(non_camel_case_types)]
pub enum Instr {
    DebugLocation(Location, String),
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
    RefGlobal {
        to: Value,
        global: ConstantRef,
        type_: Type,
    },
    Global {
        to: Value,
        global: ConstantRef,
    },
    // to = of.member
    Member {
        to: Value,
        of: Value,
        member: Member,
    },
    // @Temp: This isn't a necessary instruction, but it's nice to have
    // for hardcoded things that are emitted.
    // to.member = of
    MoveToMemberOfValue {
        to: Value,
        of: Value,
        member: Member,
    },
    // to = &(*of).member
    PointerToMemberOfPointer {
        to: Value,
        of: Value,
        member: Member,
    },
    // to = from
    Move { to: Value, from: Value },
    // *to = from
    MoveToPointer { to: Value, from: Value },
    // to = *from
    Dereference {
        to: Value,
        from: Value,
    },
    // to = &from
    Reference {
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

#[derive(Debug, Clone, Copy)]
pub struct Member {
    pub offset: usize,
    pub name: Ustr,
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

    pub fn create_with_name(&mut self, _types: &TypeSystem, _value: TypeId, type_: impl Into<Type>, name: Option<Ustr>) -> Value {
        self.create_min_align_with_name(type_.into(), 1, name)
    }

    pub fn create(&mut self, _types: &TypeSystem, _value: TypeId, type_: impl Into<Type>) -> Value {
        self.create_min_align(type_.into(), 1)
    }

    pub fn zst(&mut self) -> Value {
        self.create_min_align(TypeKind::Empty, 1)
    }

    pub fn create_min_align(&mut self, type_: impl Into<Type>, min_align: usize) -> Value {
        self.create_min_align_with_name(type_, min_align, None)
    }

    pub fn create_min_align_with_name(&mut self, type_: impl Into<Type>, min_align: usize, name: Option<Ustr>) -> Value {
        let type_ = type_.into();
        let mut align = type_.align();
        if align < min_align {
            align = min_align;
        }
        self.buffer_head = to_align(self.buffer_head, align);
        let value = Value(self.locals.len(), type_);
        self.locals.push(Register {
            offset: self.buffer_head,
            name,
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
    pub name: Option<Ustr>,
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
pub struct Value(pub usize, pub Type);

impl fmt::Display for Value {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "{} {}", self.1, self.0)
    }
}

unsafe impl Send for Value {}
unsafe impl Sync for Value {}

impl Value {
    pub fn type_(&self) -> Type {
        self.1
    }

    pub fn size(&self) -> usize {
        self.type_().size()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LabelId(pub usize);
