use crate::layout::Layout;
use crate::operators::{BinaryOp, UnaryOp};
use crate::location::Location;
use crate::program::{constant::ConstantRef, BuiltinFunction};
use crate::types::{to_align};
use std::fmt;
use ustr::Ustr;

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub enum PrimitiveType {
    Bool,
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

impl PrimitiveType {
    pub fn signed(&self) -> bool {
        matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64)
    }

    pub fn size(&self) -> usize {
        match self {
            Self::Bool | Self::U8 | Self::I8 => 1,
            Self::U16 | Self::I16 => 2,
            Self::U32 | Self::I32 | Self::F32 => 4,
            Self::U64 | Self::I64 | Self::F64 => 8,
        }
    }
    
    pub fn is_float(&self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TypedLayout {
    pub primitive: Option<PrimitiveType>,
    pub layout: Layout,
}

impl std::ops::Deref for TypedLayout {
    type Target = Layout;

    fn deref(&self) -> &Self::Target {
        &self.layout
    }
}

impl std::ops::DerefMut for TypedLayout {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.layout
    }
}

impl TypedLayout {
    pub const ZST: TypedLayout = TypedLayout {
        primitive: None,
        layout: Layout::ZST,
    };

    pub const PTR: TypedLayout = TypedLayout {
        primitive: Some(PrimitiveType::U64),
        layout: Layout::PTR,
    };
    
    pub fn size(&self) -> usize {
        self.layout.size
    }

    pub fn align(&self) -> usize {
        self.layout.align
    }
}

#[derive(Clone, Debug)]
#[allow(non_camel_case_types)]
pub enum Instr {
    DebugLocation(Location),
    Call {
        to: (StackValue, TypedLayout),
        pointer: StackValue,
        // FIXME: We don't really want a vector here, we want a more efficient datastructure
        args: Vec<(StackValue, TypedLayout)>,
        loc: Location,
    },
    // TODO: We want this to take a pointer as well. Do we want some way to generically
    // take either a pointer, or a stack value?
    SetToZero {
        to_ptr: StackValue,
        size: usize,
    },
    Binary {
        to: StackValue,
        a: StackValue,
        b: StackValue,
        op: BinaryOp,
        type_: PrimitiveType,
    },
    BinaryImm {
        to: StackValue,
        a: StackValue,
        b: u64,
        op: BinaryOp,
        type_: PrimitiveType,
    },
    IncrPtr {
        to: StackValue,
        amount: StackValue,
        scale: usize,
    },
    Unary {
        to: StackValue,
        from: StackValue,
        op: UnaryOp,
        type_: PrimitiveType,
    },
    RefGlobal {
        to_ptr: StackValue,
        global: ConstantRef,
    },
    StackPtr {
        to: StackValue,
        take_pointer_to: StackValue,
    },
    Move {
        to: StackValue,
        from: StackValue,
        size: usize,
    },
    MoveImm {
        to: StackValue,
        from: [u8; 8],
        size: usize,
    },
    IndirectMove {
        to_ptr: StackValue,
        offset: usize,
        from: StackValue,
        size: usize,
    },
    Dereference {
        to: StackValue,
        from_ptr: StackValue,
        offset: usize,
        size: usize,
    },
    ConvertNum {
        to: StackValue,
        from: StackValue,
        to_number: PrimitiveType,
        from_number: PrimitiveType,
    },
    // jump to 'to' if condition
    JumpIfZero {
        condition: StackValue,
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
    pub args: Vec<(StackValue, TypedLayout)>,
    pub result: StackValue,
    pub result_layout: TypedLayout,
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

    pub fn create(&mut self, align: usize, size: usize) -> StackValue {
        debug_assert_ne!(size, 0);
        debug_assert!(size >= align);

        self.head = to_align(self.head, align);
        self.values.push(StackValueInfo {
            location: self.head,
            size,
        });
        let value = StackValue(self.head);
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
    pub fn value(&self) -> StackValue {
        StackValue(self.location)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct StackValue(pub usize);

impl StackValue {
    pub const ZST: Self = Self(0);
}

impl fmt::Display for StackValue {
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
