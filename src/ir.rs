use crate::layout::Layout;
use crate::operators::{BinaryOp, UnaryOp};
use crate::location::Location;
use crate::program::{constant::ConstantRef, BuiltinFunction};
use crate::types::{to_align};
use std::fmt;
use ustr::Ustr;

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub enum NumberType {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
}

impl NumberType {
    pub fn signed(&self) -> bool {
        matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64)
    }

    pub fn size(&self) -> usize {
        match self {
            Self::U8 | Self::I8 => 1,
            Self::U16 | Self::I16 => 2,
            Self::U32 | Self::I32 | Self::F32 => 4,
            Self::U64 | Self::I64 | Self::F64 => 8,
        }
    }
    
    pub fn is_float(&self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }
}

#[derive(Clone, Debug)]
#[allow(non_camel_case_types)]
pub enum Instr {
    DebugLocation(Location),
    Call {
        to: (Value, Layout),
        pointer: Value,
        // FIXME: We don't really want a vector here, we want a more efficient datastructure
        args: Vec<(Value, Layout)>,
        loc: Location,
    },
    SetToZero {
        to_ptr: Value,
        size: usize,
    },
    Binary {
        to: Value,
        a: Value,
        b: Value,
        op: BinaryOp,
        type_: NumberType,
    },
    BinaryImm {
        to: Value,
        a: Value,
        b: u64,
        op: BinaryOp,
        type_: NumberType,
    },
    IncrPtr {
        to: Value,
        amount: Value,
        scale: usize,
    },
    Unary {
        to: Value,
        from: Value,
        op: UnaryOp,
        type_: NumberType,
    },
    RefGlobal {
        to_ptr: Value,
        global: ConstantRef,
    },
    StackPtr {
        to: Value,
        take_pointer_to: Value,
    },
    Move {
        to: Value,
        from: Value,
        size: usize,
    },
    MoveImm {
        to: Value,
        from: [u8; 8],
        size: usize,
    },
    IndirectMove {
        to_ptr: Value,
        from: Value,
        size: usize,
    },
    Dereference {
        to: Value,
        from_ptr: Value,
        size: usize,
    },
    ConvertNum {
        to: Value,
        from: Value,
        to_number: NumberType,
        from_number: NumberType,
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

pub enum Routine {
    Builtin(BuiltinFunction),
    UserDefined(UserDefinedRoutine),
    Extern(Ustr),
}

pub struct UserDefinedRoutine {
    pub loc: Location,
    pub name: Ustr,
    pub label_locations: Vec<usize>,
    pub instr: Vec<Instr>,
    pub stack: StackAllocator,
    pub result: Value,
}

pub struct StackAllocator {
    pub values: Vec<StackValueInfo>,
    pub head: usize,
    pub max: usize,
}

impl StackAllocator {
    pub fn new() -> Self {
        Self {
            values: Vec::new(),
            head: 0,
            max: 0,
        }
    }

    pub fn create(&mut self, align: usize, size: usize) -> Value {
        debug_assert_ne!(size, 0);
        debug_assert!(size >= align);

        self.head = to_align(self.head, align);
        self.values.push(StackValueInfo {
            location: self.head,
            size,
        });
        let value = Value(self.head);
        self.head += size;
        self.max = self.head.max(self.max);
        value
    }
}

pub struct StackValueInfo {
    pub location: usize,
    pub size: usize,
}

impl StackValueInfo {
    pub fn value(&self) -> Value {
        Value(self.location)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Value(pub usize);

impl Value {
    pub const ZST: Self = Self(0);
}

impl fmt::Display for Value {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "r{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LabelId(pub usize);

impl fmt::Display for LabelId {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "L{}", self.0)
    }
}
