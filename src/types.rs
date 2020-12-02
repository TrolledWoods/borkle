use lazy_static::lazy_static;
use parking_lot::Mutex;
use std::collections::HashSet;
use std::fmt::{self, Debug, Display};
use std::hash::{Hash, Hasher};
use ustr::Ustr;

lazy_static! {
    static ref TYPES: Mutex<HashSet<&'static TypeData>> = Mutex::new(HashSet::new());
}

#[derive(Clone, Copy)]
pub struct Type(&'static TypeData);

impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.0 as *const TypeData).hash(state);
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl Eq for Type {}

impl Debug for Type {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.kind.fmt(fmt)
    }
}

impl Display for Type {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.kind.fmt(fmt)
    }
}

impl From<TypeKind> for Type {
    fn from(other: TypeKind) -> Self {
        Self::new(other)
    }
}

impl Type {
    pub fn new(kind: TypeKind) -> Self {
        let (size, align) = kind.calculate_size_align();

        let data = TypeData { size, align, kind };
        let mut types = TYPES.lock();
        if let Some(content) = types.get(&data) {
            Self(content)
        } else {
            let leaked = Box::leak(Box::new(data));
            types.insert(leaked);
            Self(leaked)
        }
    }

    pub fn layout(self) -> std::alloc::Layout {
        unsafe { std::alloc::Layout::from_size_align_unchecked(self.size(), self.align()) }
    }

    pub const fn size(self) -> usize {
        self.0.size
    }

    pub const fn align(self) -> usize {
        self.0.align
    }

    pub const fn kind(self) -> &'static TypeKind {
        &self.0.kind
    }

    pub fn member(self, member_name: Ustr) -> Option<Member> {
        match self.kind() {
            TypeKind::Struct(members) => {
                let mut byte_offset = 0;
                for &(name, type_) in members {
                    byte_offset = to_align(byte_offset, type_.align());

                    if name == member_name {
                        return Some(Member {
                            parent_type: self,
                            byte_offset,
                            type_,
                        });
                    }

                    byte_offset += type_.size();
                }

                None
            }
            TypeKind::Buffer(internal) => match member_name.as_str() {
                "ptr" => Some(Member {
                    parent_type: self,
                    byte_offset: 0,
                    type_: Type::new(TypeKind::Reference(*internal)),
                }),
                "len" => Some(Member {
                    parent_type: self,
                    byte_offset: 8,
                    type_: Type::new(TypeKind::Int(IntTypeKind::Usize)),
                }),
                _ => None,
            },
            _ => None,
        }
    }
}

#[derive(Hash, PartialEq, Eq)]
struct TypeData {
    size: usize,
    align: usize,
    kind: TypeKind,
}

impl Display for TypeKind {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => write!(fmt, "()"),
            Self::F64 => write!(fmt, "f64"),
            Self::F32 => write!(fmt, "f32"),
            Self::Int(int) => int.fmt(fmt),
            Self::Bool => write!(fmt, "bool"),
            Self::Reference(internal) => write!(fmt, "&{}", internal),
            Self::Buffer(internal) => write!(fmt, "[] {}", internal),
            Self::Array(internal, length) => write!(fmt, "[{}] {}", length, internal),
            Self::Function {
                args,
                returns,
                is_extern,
            } => {
                if *is_extern {
                    write!(fmt, "extern ")?;
                }
                write!(fmt, "fn(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(fmt, ", ")?;
                    }
                    write!(fmt, "{}", arg)?;
                }

                write!(fmt, ")")?;
                if !matches!(returns.kind(), Self::Empty) {
                    write!(fmt, " -> {}", returns)?;
                }
                Ok(())
            }
            Self::Struct(members) => {
                write!(fmt, "{{")?;
                for (i, (name, member)) in members.iter().enumerate() {
                    if i > 0 {
                        write!(fmt, ", ")?;
                    }
                    write!(fmt, "{}: {}", name, member)?;
                }
                write!(fmt, "}}")?;
                Ok(())
            }
        }
    }
}

/// FIXME: I think this should be called `align_to`
pub fn to_align(value: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (value + align - 1) & !(align - 1)
}

#[derive(Hash, PartialEq, Eq)]
pub enum TypeKind {
    Empty,
    F64,
    F32,
    Bool,
    Int(IntTypeKind),
    Array(Type, usize),
    Reference(Type),
    Buffer(Type),
    Function {
        args: Vec<Type>,
        returns: Type,
        is_extern: bool,
    },
    Struct(Vec<(Ustr, Type)>),
}

impl TypeKind {
    fn calculate_size_align(&self) -> (usize, usize) {
        match self {
            Self::Empty => (0, 1),
            Self::F64 | Self::Reference(_) | Self::Function { .. } => (8, 8),
            Self::Buffer(_) => (16, 8),
            Self::F32 => (4, 4),
            Self::Bool => (1, 1),
            Self::Array(internal, length) => {
                let (member_size, align) = internal.kind().calculate_size_align();
                let member_size = to_align(member_size, align);
                (member_size * length, align)
            }
            Self::Int(kind) => kind.size_align(),
            Self::Struct(members) => {
                let mut size = 0;
                let mut align = 1;
                for (_, member) in members {
                    size += member.size();
                    if member.align() > align {
                        align = member.align();
                    }
                    size = to_align(size, member.align());
                }
                size = to_align(size, align);
                (size, align)
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntTypeKind {
    Usize,
    Isize,
    I64,
    U64,
    I32,
    U32,
    I16,
    U16,
    I8,
    U8,
}

impl IntTypeKind {
    pub fn range(self) -> std::ops::RangeInclusive<i128> {
        match self {
            Self::U64 | Self::Usize => u64::MIN.into()..=u64::MAX.into(),
            Self::I64 | Self::Isize => i64::MIN.into()..=i64::MAX.into(),
            Self::U32 => u32::MIN.into()..=u32::MAX.into(),
            Self::I32 => i32::MIN.into()..=i32::MAX.into(),
            Self::U16 => u16::MIN.into()..=u16::MAX.into(),
            Self::I16 => i16::MIN.into()..=i16::MAX.into(),
            Self::U8 => u8::MIN.into()..=u8::MAX.into(),
            Self::I8 => i8::MIN.into()..=i8::MAX.into(),
        }
    }

    #[inline]
    pub fn size_align(self) -> (usize, usize) {
        match self {
            Self::Usize | Self::Isize => (8, 8),
            Self::U64 | Self::I64 => (8, 8),
            Self::U32 | Self::I32 => (4, 4),
            Self::U16 | Self::I16 => (2, 2),
            Self::U8 | Self::I8 => (1, 1),
        }
    }
}

impl From<IntTypeKind> for Type {
    fn from(int: IntTypeKind) -> Type {
        Type::new(TypeKind::Int(int))
    }
}

impl Debug for IntTypeKind {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Usize => write!(fmt, "usize"),
            Self::Isize => write!(fmt, "isize"),
            Self::I64 => write!(fmt, "i64"),
            Self::U64 => write!(fmt, "u64"),
            Self::I32 => write!(fmt, "i32"),
            Self::U32 => write!(fmt, "u32"),
            Self::I16 => write!(fmt, "i16"),
            Self::U16 => write!(fmt, "u16"),
            Self::I8 => write!(fmt, "i8"),
            Self::U8 => write!(fmt, "u8"),
        }
    }
}

pub struct Member {
    pub parent_type: Type,
    pub byte_offset: usize,
    pub type_: Type,
}
