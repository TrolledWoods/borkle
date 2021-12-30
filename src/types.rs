use crate::location::Location;
use crate::program::FunctionId;
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
        if let Some((_, name)) = self.0.name {
            return write!(fmt, "{}", name);
        }

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
        let mut types = TYPES.lock();
        Self::new_without_lock(&mut *types, kind)
    }

    fn new_without_lock(types: &mut Vec<&'static TypeData>, kind: TypeKind) -> Self {
        if let Some(content) = types
            .iter()
            .filter(|c| !c.is_unique)
            .find(|&&c| c.kind == kind)
        {
            Self(content)
        } else {
            Self::new_unique(types, kind, None, Vec::new(), false)
        }
    }

    fn new_unique(
        types: &mut Vec<&'static TypeData>,
        kind: TypeKind,
        name: Option<(Location, Ustr)>,
        aliases: Vec<Alias>,
        is_unique: bool,
    ) -> Type {
        let (size, align) = kind.calculate_size_align();
        let can_be_stored_in_constant = kind.can_be_stored_in_constant();

        let mut pointers = Vec::new();
        kind.get_pointers(types, &mut pointers);

        let data = TypeData {
            name,
            is_unique,
            aliases,
            members: kind.get_members(types),
            is_pointer_to_zst: matches!(kind, TypeKind::Reference { pointee: inner, .. } | TypeKind::Buffer { pointee: inner, .. } if inner.size() == 0),
            size,
            align,
            kind,
            pointers,
            can_be_stored_in_constant,
        };
        let leaked = Box::leak(Box::new(data));
        types.push(leaked);
        Self(leaked)
    }

    pub fn pointing_to(self) -> Option<Type> {
        if let TypeKind::Reference { pointee, .. } = *self.kind() {
            Some(pointee)
        } else {
            None
        }
    }

    pub fn is_pointer_to_zst(self) -> bool {
        self.0.is_pointer_to_zst
    }

    pub fn can_be_stored_in_constant(self) -> bool {
        self.0.can_be_stored_in_constant
    }

    pub unsafe fn get_function_ids(
        self,
        value: *const u8,
    ) -> impl Iterator<Item = FunctionId> + 'static {
        self.pointers()
            .iter()
            .filter_map(move |(offset, kind)| match kind {
                PointerInType::Function { .. } => Some(*value.add(*offset).cast::<FunctionId>()),
                _ => None,
            })
    }

    pub fn pointers(self) -> &'static [(usize, PointerInType)] {
        &self.0.pointers
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
        for &(name, offset, type_) in &self.0.members {
            if name == member_name {
                return Some(Member {
                    byte_offset: offset,
                    indirections: 1,
                    type_,
                });
            }
        }

        for &Alias {
            name,
            offset,
            indirections,
            type_,
        } in &self.0.aliases
        {
            if name == member_name {
                return Some(Member {
                    byte_offset: offset,
                    indirections,
                    type_,
                });
            }
        }

        None
    }
}

pub struct TypeData {
    pub kind: TypeKind,
    is_unique: bool,
    pub members: Vec<(Ustr, usize, Type)>,
    pub aliases: Vec<Alias>,

    pub name: Option<(Location, Ustr)>,

    pub size: usize,
    align: usize,

    pointers: Vec<(usize, PointerInType)>,

    can_be_stored_in_constant: bool,
    pub is_pointer_to_zst: bool,
}

impl Display for TypeKind {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Range(inner) => write!(fmt, "{0}..{0}", inner),
            Self::VoidBuffer => write!(fmt, "[] void"),
            Self::VoidPtr => write!(fmt, "&void"),
            Self::AnyPtr => write!(fmt, "&any"),
            Self::Type => write!(fmt, "type"),
            Self::Empty => write!(fmt, "()"),
            Self::F64 => write!(fmt, "f64"),
            Self::F32 => write!(fmt, "f32"),
            Self::Int(int) => int.fmt(fmt),
            Self::Bool => write!(fmt, "bool"),
            Self::Reference { pointee } => write!(fmt, "&{}", pointee),
            Self::Buffer { pointee } => write!(fmt, "[] {}", pointee),
            Self::Array(internal, length) => write!(fmt, "[{}] {}", length, internal),
            Self::Function { args, returns } => {
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
            Self::Tuple(members) => {
                write!(fmt, "(")?;
                for (i, member) in members.iter().enumerate() {
                    if i > 0 {
                        write!(fmt, ", ")?;
                    }
                    write!(fmt, "{}", member)?;
                }
                write!(fmt, ")")?;
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

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum TypeKind {
    Type,
    Empty,
    F64,
    F32,
    Bool,
    AnyPtr,
    VoidPtr,
    VoidBuffer,
    Range(Type),
    Int(IntTypeKind),
    Array(Type, usize),
    Reference { pointee: Type },
    Buffer { pointee: Type },
    Function { args: Vec<Type>, returns: Type },
    Struct(Vec<(Ustr, Type)>),
    Tuple(Vec<Type>),
}

impl TypeKind {
    fn for_each_child(&self, mut on_inner: impl FnMut(Type)) {
        match self {
            TypeKind::Type
            | TypeKind::AnyPtr
            | TypeKind::VoidPtr
            | TypeKind::VoidBuffer
            | TypeKind::Empty
            | TypeKind::F64
            | TypeKind::F32
            | TypeKind::Bool
            | TypeKind::Int(_) => {}
            TypeKind::Buffer { pointee: inner, .. }
            | TypeKind::Array(inner, _)
            | TypeKind::Range(inner)
            | TypeKind::Reference { pointee: inner, .. } => on_inner(*inner),
            TypeKind::Function { args, returns, .. } => {
                for arg in args {
                    on_inner(*arg);
                }

                on_inner(*returns);
            }
            TypeKind::Tuple(members) => {
                for member in members {
                    on_inner(*member);
                }
            }
            TypeKind::Struct(members) => {
                for (_, member) in members {
                    on_inner(*member);
                }
            }
        }
    }

    fn get_members(&self, types: &mut Vec<&'static TypeData>) -> Vec<(Ustr, usize, Type)> {
        match *self {
            TypeKind::Buffer { pointee, } => {
                let ptr_type = Type::new_without_lock(
                    types,
                    TypeKind::Reference {
                        pointee,
                    },
                );
                let usize_type = Type::new_without_lock(types, TypeKind::Int(IntTypeKind::Usize));
                vec![("ptr".into(), 0, ptr_type), ("len".into(), 8, usize_type)]
            }
            TypeKind::AnyPtr => {
                let ptr_type = Type::new_without_lock(types, TypeKind::VoidPtr);
                let type_type = Type::new_without_lock(types, TypeKind::Type);
                vec![("ptr".into(), 0, ptr_type), ("type_".into(), 8, type_type)]
            }
            TypeKind::VoidBuffer => {
                let ptr_type = Type::new_without_lock(types, TypeKind::VoidPtr);
                let usize_type = Type::new_without_lock(types, TypeKind::Int(IntTypeKind::Usize));
                vec![("ptr".into(), 0, ptr_type), ("len".into(), 8, usize_type)]
            }
            TypeKind::Struct(ref members) => {
                let mut new_members = Vec::new();
                for (name, offset, type_) in struct_field_offsets(members.iter().copied()) {
                    new_members.push((name, offset, type_));
                }
                new_members
            }
            TypeKind::Tuple(ref members) => {
                let mut new_members = Vec::new();
                for (name, offset, type_) in struct_field_offsets(members.iter().enumerate().map(|(i, v)| (format!("_{}", i).into(), *v))) {
                    new_members.push((name, offset, type_));
                }
                new_members
            }
            TypeKind::Range(internal) => {
                vec![
                    ("start".into(), 0, internal),
                    (
                        "end".into(),
                        to_align(internal.size(), internal.align()),
                        internal,
                    ),
                ]
            }
            TypeKind::Array(inner, length) => {
                let mut members = Vec::with_capacity(length);
                let mut pos = 0;
                for i in 0..length {
                    members.push((format!("_{}", i).into(), pos, inner));
                    pos += inner.size();
                }
                members
            }
            _ => Vec::new(),
        }
    }

    fn can_be_stored_in_constant(&self) -> bool {
        match self {
            TypeKind::Array(_, 0) | TypeKind::Function { .. } => true,
            TypeKind::VoidPtr | TypeKind::VoidBuffer => false,
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
            Self::Type => (8, 8),
            Self::Empty => (0, 1),
            Self::VoidPtr | Self::F64 | Self::Reference { .. } | Self::Function { .. } => (8, 8),
            Self::AnyPtr | Self::VoidBuffer | Self::Buffer { .. } => (16, 8),
            Self::F32 => (4, 4),
            Self::Bool => (1, 1),
            Self::Range(inner) => {
                let size = array_size(inner.size(), inner.align(), 2);
                (size, inner.align())
            }
            Self::Array(internal, length) => {
                let member_size = internal.size();
                let align = internal.align();
                let size = array_size(member_size, align, *length);
                (size, align)
            }
            Self::Int(kind) => kind.size_align(),
            Self::Tuple(members) => {
                let mut size = 0;
                let mut align = 1;
                for member in members {
                    size += member.size();
                    if member.align() > align {
                        align = member.align();
                    }
                    size = to_align(size, member.align());
                }
                size = to_align(size, align);
                (size, align)
            }
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
    fn get_pointers(
        &self,
        types: &mut Vec<&'static TypeData>,
        pointers: &mut Vec<(usize, PointerInType)>,
    ) {
        match self {
            Self::Type
            | Self::Empty
            | Self::Int(_)
            | Self::F32
            | Self::F64
            | Self::VoidPtr
            | Self::AnyPtr
            | Self::Bool => {}
            Self::Reference { pointee, .. }  => {
                if pointee.size() > 0 {
                    pointers.push((0, PointerInType::Pointer(*pointee)));
                }
            }
            Self::Buffer { pointee, .. } => {
                if pointee.size() > 0 {
                    pointers.push((0, PointerInType::Buffer(*pointee)));
                }
            }
            Self::VoidBuffer => {
                pointers.push((
                    0,
                    PointerInType::Buffer(Type::new_without_lock(
                        types,
                        TypeKind::Int(IntTypeKind::U8),
                    )),
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
            Self::Function { args, returns } => {
                pointers.push((
                    0,
                    PointerInType::Function {
                        args: args.clone(),
                        returns: *returns,
                    },
                ));
            }
            Self::Tuple(fields) => {
                let def_field = "".into();
                for (_, offset, field_type) in struct_field_offsets(fields.iter().copied().map(|v| (def_field, v))) {
                    for &(field_pointer_offset, ref field_pointer_type) in field_type.pointers() {
                        pointers.push((offset + field_pointer_offset, field_pointer_type.clone()));
                    }
                }
            }
            Self::Struct(fields) => {
                for (_name, offset, field_type) in struct_field_offsets(fields.iter().copied()) {
                    for &(field_pointer_offset, ref field_pointer_type) in field_type.pointers() {
                        pointers.push((offset + field_pointer_offset, field_pointer_type.clone()));
                    }
                }
            }
        }
    }
}

pub fn struct_field_offsets<'a>(
    fields: impl Iterator<Item = (Ustr, Type)> + 'a,
) -> impl Iterator<Item = (Ustr, usize, Type)> + 'a {
    fields.scan(0, |offset, (name, type_)| {
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
    Function { args: Vec<Type>, returns: Type },
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

    pub fn signed(self) -> bool {
        match self {
            Self::Usize | Self::U64 | Self::U32 | Self::U16 | Self::U8 => true,
            Self::Isize | Self::I64 | Self::I32 | Self::I16 | Self::I8 => true,
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

pub struct Alias {
    pub name: Ustr,
    pub offset: usize,
    pub indirections: usize,
    pub type_: Type,
}

pub struct Member {
    pub byte_offset: usize,
    pub indirections: usize,
    pub type_: Type,
}

fn array_size(size: usize, align: usize, num_elements: usize) -> usize {
    let element_size = to_align(size, align);
    element_size * num_elements
}
