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
                let mut bit_offset = 0;
                for &(name, type_) in members {
                    bit_offset = to_align(bit_offset, type_.align());

                    if name == member_name {
                        return Some(Member {
                            parent_type: self,
                            bit_offset,
                            type_,
                        });
                    }

                    bit_offset += type_.size();
                }

                None
            }
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
            Self::I64 => write!(fmt, "i64"),
            Self::U8 => write!(fmt, "u8"),
            Self::Reference(internal) => write!(fmt, "&{}", internal),
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
    (value + align - 1) & !align
}

#[derive(Hash, PartialEq, Eq)]
pub enum TypeKind {
    Empty,
    F64,
    I64,
    U8,
    Reference(Type),
    Struct(Vec<(Ustr, Type)>),
}

impl TypeKind {
    fn calculate_size_align(&self) -> (usize, usize) {
        match self {
            Self::Empty => (0, 1),
            Self::U8 => (1, 1),
            Self::F64 | Self::I64 | Self::Reference(_) => (8, 8),
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

pub struct Member {
    pub parent_type: Type,
    pub bit_offset: usize,
    pub type_: Type,
}
