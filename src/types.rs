use lazy_static::lazy_static;
use parking_lot::Mutex;
use std::fmt::{self, Debug, Display};
use std::hash::{Hash, Hasher};
use ustr::Ustr;

lazy_static! {
    pub static ref TYPES: Mutex<Vec<&'static TypeData>> = Mutex::new(Vec::new());
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Type(pub &'static TypeData);

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
        let can_be_stored_in_constant = kind.can_be_stored_in_constant();

        let mut is_never_type = matches!(kind, TypeKind::Never);
        kind.for_each_child(|child| {
            if child.0.is_never_type {
                is_never_type = true
            }
        });

        let mut pointers = Vec::new();
        kind.get_pointers(&mut pointers);

        let data = TypeData {
            call_scheme: kind.call_scheme(),
            is_never_type,
            size,
            align,
            kind,
            pointers,
            can_be_stored_in_constant,
        };
        let mut types = TYPES.lock();
        if let Some(content) = types.iter().find(|&&c| c == &data) {
            Self(content)
        } else {
            let leaked = Box::leak(Box::new(data));
            types.push(leaked);
            Self(leaked)
        }
    }

    pub fn call_scheme(self) -> Option<&'static (Vec<Type>, Type)> {
        self.0.call_scheme.as_ref()
    }

    pub fn can_be_stored_in_constant(self) -> bool {
        self.0.can_be_stored_in_constant
    }

    pub fn is_never_type(self) -> bool {
        self.0.is_never_type
    }

    pub fn pointers(self) -> &'static [(usize, PointerInType)] {
        &self.0.pointers
    }

    #[inline]
    pub fn as_ptr(self) -> *const u8 {
        self.0 as *const TypeData as *const _
    }

    #[inline]
    pub const fn size(self) -> usize {
        self.0.size
    }

    #[inline]
    pub const fn align(self) -> usize {
        self.0.align
    }

    #[inline]
    pub const fn kind(self) -> &'static TypeKind {
        &self.0.kind
    }

    pub fn member(self, member_name: Ustr) -> Option<Member> {
        match self.kind() {
            TypeKind::Struct(members) => {
                for (name, offset, type_) in struct_field_offsets(members) {
                    if name == member_name {
                        return Some(Member {
                            parent_type: self,
                            byte_offset: offset,
                            type_,
                        });
                    }
                }

                None
            }
            TypeKind::Range(internal) => match member_name.as_str() {
                "start" => Some(Member {
                    parent_type: self,
                    byte_offset: 0,
                    type_: *internal,
                }),
                "end" => Some(Member {
                    parent_type: self,
                    byte_offset: to_align(internal.size(), internal.align()),
                    type_: *internal,
                }),
                _ => None,
            },
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
            TypeKind::AnyBuffer => match member_name.as_str() {
                "ptr" => Some(Member {
                    parent_type: self,
                    byte_offset: 0,
                    type_: Type::new(TypeKind::Any),
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
pub struct TypeData {
    is_never_type: bool,
    size: usize,
    align: usize,
    pub kind: TypeKind,
    call_scheme: Option<(Vec<Type>, Type)>,
    pointers: Vec<(usize, PointerInType)>,
    can_be_stored_in_constant: bool,
}

impl Display for TypeKind {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Intrinsic(inner) => write!(fmt, "{}", inner),
            Self::Range(inner) => write!(fmt, "{0}..{0}", inner),
            Self::AnyBuffer => write!(fmt, "[] any"),
            Self::Any => write!(fmt, "&any"),
            Self::Never => write!(fmt, "!"),
            Self::Type => write!(fmt, "type"),
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
    Intrinsic(crate::intrinsic::Intrinsic),
    Never,
    Type,
    Empty,
    F64,
    F32,
    Bool,
    Any,
    AnyBuffer,
    Range(Type),
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
    fn for_each_child(&self, mut on_inner: impl FnMut(Type)) {
        match self {
            TypeKind::Never
            | TypeKind::Type
            | TypeKind::Any
            | TypeKind::AnyBuffer
            | TypeKind::Empty
            | TypeKind::F64
            | TypeKind::F32
            | TypeKind::Bool
            | TypeKind::Intrinsic(_)
            | TypeKind::Int(_) => {}
            TypeKind::Buffer(inner)
            | TypeKind::Array(inner, _)
            | TypeKind::Range(inner)
            | TypeKind::Reference(inner) => on_inner(*inner),
            TypeKind::Function { args, returns, .. } => {
                for arg in args {
                    on_inner(*arg);
                }

                on_inner(*returns);
            }
            TypeKind::Struct(members) => {
                for (_, member) in members {
                    on_inner(*member);
                }
            }
        }
    }

    fn call_scheme(&self) -> Option<(Vec<Type>, Type)> {
        match self {
            TypeKind::Function { args, returns, .. } => Some((args.clone(), *returns)),
            TypeKind::Intrinsic(inner) => Some(inner.get_function_data()),
            _ => None,
        }
    }

    fn can_be_stored_in_constant(&self) -> bool {
        match self {
            TypeKind::Array(_, 0) | TypeKind::Function { .. } => true,
            TypeKind::Any | TypeKind::AnyBuffer | TypeKind::Never => false,
            _ => {
                let mut can_be = true;
                self.for_each_child(|child| {
                    if !child.can_be_stored_in_constant() {
                        can_be = false;
                    }
                });
                can_be
            }
        }
    }

    fn calculate_size_align(&self) -> (usize, usize) {
        match self {
            Self::Never => (0, 0),
            Self::Type => (8, 8),
            Self::Intrinsic(_) | Self::Empty => (0, 1),
            Self::Any | Self::F64 | Self::Reference(_) | Self::Function { .. } => (8, 8),
            Self::AnyBuffer | Self::Buffer(_) => (16, 8),
            Self::F32 => (4, 4),
            Self::Bool => (1, 1),
            Self::Range(inner) => {
                let size = array_size(inner.size(), inner.align(), 2);
                (size, inner.align())
            }
            Self::Array(internal, length) => {
                let (member_size, align) = internal.kind().calculate_size_align();
                let size = array_size(member_size, align, *length);
                (size, align)
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

    /// Appends all the pointers in this type to a vector, with the offset offsetted by the offset. Does not include indirect
    /// pointers(i.e. pointers behind other pointers).
    fn get_pointers(&self, pointers: &mut Vec<(usize, PointerInType)>) {
        match self {
            Self::Never
            | Self::Type
            | Self::Empty
            | Self::Int(_)
            | Self::F32
            | Self::F64
            | Self::Any
            | Self::Intrinsic(_)
            | Self::Bool => {}
            Self::Reference(internal) => {
                if internal.size() > 0 {
                    pointers.push((0, PointerInType::Pointer(*internal)));
                }
            }
            Self::Buffer(internal) => {
                if internal.size() > 0 {
                    pointers.push((0, PointerInType::Buffer(*internal)));
                }
            }
            Self::AnyBuffer => {
                pointers.push((
                    0,
                    PointerInType::Buffer(Type::new(TypeKind::Int(IntTypeKind::U8))),
                ));
            }
            Self::Range(internal) => {
                let second_element = to_align(internal.size(), internal.align());
                for (internal_offset, internal_type) in internal.pointers() {
                    pointers.push((*internal_offset, internal_type.clone()));
                    pointers.push((second_element + *internal_offset, internal_type.clone()));
                }
            }
            Self::Array(internal, len) => {
                let element_offset = to_align(internal.size(), internal.align());
                for i in 0..*len {
                    for (internal_offset, internal_type) in internal.pointers() {
                        pointers
                            .push((i * element_offset + internal_offset, internal_type.clone()));
                    }
                }
            }
            Self::Function {
                args,
                returns,
                is_extern,
            } => {
                pointers.push((
                    0,
                    PointerInType::Function {
                        args: args.clone(),
                        returns: *returns,
                        is_extern: *is_extern,
                    },
                ));
            }
            Self::Struct(fields) => {
                for (_name, offset, field_type) in struct_field_offsets(fields) {
                    for &(field_pointer_offset, ref field_pointer_type) in field_type.pointers() {
                        pointers.push((offset + field_pointer_offset, field_pointer_type.clone()));
                    }
                }
            }
        }
    }
}

pub fn struct_field_offsets(
    fields: &[(Ustr, Type)],
) -> impl Iterator<Item = (Ustr, usize, Type)> + '_ {
    fields.iter().scan(0, |offset, &(name, type_)| {
        *offset = to_align(*offset, type_.align());
        let field_offset = *offset;
        *offset += type_.size();
        Some((name, field_offset, type_))
    })
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub enum PointerInType {
    Pointer(Type),
    Buffer(Type),
    // FIXME: This 'Vec' here is fairly inefficient
    Function {
        args: Vec<Type>,
        returns: Type,
        is_extern: bool,
    },
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

#[repr(C)]
#[derive(Clone, Copy)]
pub struct BufferRepr {
    pub ptr: *mut u8,
    pub length: usize,
}

pub struct Member {
    pub parent_type: Type,
    pub byte_offset: usize,
    pub type_: Type,
}

fn array_size(size: usize, align: usize, num_elements: usize) -> usize {
    let element_size = to_align(size, align);
    element_size * num_elements
}
