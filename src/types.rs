use crate::location::Location;
use crate::layout::{Layout, StructLayout};
use crate::program::{constant_to_str, FunctionId};
use std::fmt::{self, Debug, Display};
use ustr::Ustr;
// TODO: Move over TypeKind here, because I think it makes more sense to define generic type stuff
// in here now.
// pub use crate::type_infer::{self, TypeKind};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Type(TypeData);

impl Debug for Type {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(fmt)
    }
}

impl Display for Type {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(fmt)
    }
}

impl From<TypeKind> for Type {
    fn from(other: TypeKind) -> Self {
        Self::new(other)
    }
}

impl Type {
    pub fn new_float(size: u8) -> Self {
        debug_assert!(size == 4 || size == 8);

        let size = Self::new(TypeKind::IntSize(size));
        Self::new_with_args(TypeKind::Float, Box::new([size]))
    }

    pub fn new_int(int_kind: IntTypeKind) -> Self {
        let (signed, size) = match int_kind {
            IntTypeKind::U8    => (false, 1),
            IntTypeKind::U16   => (false, 2),
            IntTypeKind::U32   => (false, 4),
            IntTypeKind::U64   => (false, 8),
            IntTypeKind::Usize => (false, 0),
            IntTypeKind::I8    => (true,  1),
            IntTypeKind::I16   => (true,  2),
            IntTypeKind::I32   => (true,  4),
            IntTypeKind::I64   => (true,  8),
            IntTypeKind::Isize => (true,  0),
        };

        let signed = Self::new(TypeKind::IntSigned(signed));
        let size = Self::new(TypeKind::IntSize(size));

        Self::new_with_args(TypeKind::Int, Box::new([signed, size]))
    }

    pub fn new(kind: TypeKind) -> Self {
        profile::profile!("Type::new");
        Self::new_unique(kind, Box::new([]))
    }
    
    pub fn new_with_args(kind: TypeKind, args: Box<[Type]>) -> Self {
        profile::profile!("Type::new");
        Self::new_unique(kind, args)
    }

    fn new_unique(
        kind: TypeKind,
        args: Box<[Type]>,
    ) -> Type {
        let mut data = TypeData {
            // @Cleanup: Temporary value, not that nice
            layout: Layout { size: 0, align: 0 },
            kind,
            args,
        };

        let (size, align) = data.calculate_size_align();
        data.layout = Layout { size, align };

        Self(data)
    }

    pub fn can_be_stored_in_constant(&self) -> bool {
        match self.kind() {
            TypeKind::Function { .. } => true,
            _ => {
                let mut can_be = true;
                self.0.for_each_child(|child| {
                    if !child.can_be_stored_in_constant() {
                        can_be = false;
                    }
                });
                can_be
            }
        }
    }

    pub unsafe fn get_function_ids(
        &self,
        value: *const u8,
        mut add_function_id: impl FnMut(FunctionId),
    ) {
        self.get_pointers(|offset, kind| {
            match kind {
                PointerInType::Function { .. } => add_function_id(*value.add(offset).cast::<FunctionId>()),
                _ => {},
            }
        });
    }

    #[inline]
    pub fn get_pointers<'a>(&'a self, mut add_pointer: impl FnMut(usize, PointerInType<'a>)) {
        self.get_pointers_internal(0, &mut add_pointer);
    }

    unsafe fn read_constant_as_usize(&self) -> usize {
        let TypeKind::ConstantValue(value) = self.args()[1].kind() else { unreachable!() };
        *value.as_ptr().cast::<usize>()
    }

    fn get_pointers_internal<'a>(
        &'a self,
        base_offset: usize,
        add_pointer: &mut impl FnMut(usize, PointerInType<'a>)
    ) {
        match self.kind() {
            TypeKind::Empty
            | TypeKind::Int
            | TypeKind::Float
            | TypeKind::IntSize(_)
            | TypeKind::IntSigned(_)
            | TypeKind::ConstantValue(_) 
            | TypeKind::Constant
            | TypeKind::Bool => {}
            TypeKind::CompareUnspecified => unreachable!(),
            TypeKind::Reference => {
                let pointee = &self.args()[0];
                if pointee.size() > 0 {
                    add_pointer(base_offset, PointerInType::Pointer(pointee));
                }
            }
            TypeKind::Buffer => {
                let pointee = &self.args()[0];
                if pointee.size() > 0 {
                    add_pointer(base_offset, PointerInType::Buffer(pointee));
                }
            }
            TypeKind::Array => {
                let internal = &self.args()[0];
                let len = unsafe { self.args()[1].read_constant_as_usize() };
                let element_offset = internal.size();
                for i in 0..len {
                    internal.get_pointers_internal(base_offset + i * element_offset, add_pointer);
                }
            }
            TypeKind::Function => {
                add_pointer(
                    base_offset,
                    PointerInType::Function(self.args()),
                );
            }
            TypeKind::Tuple | TypeKind::Struct(_) => {
                let mut layout = StructLayout::new(0);
                for field in self.args() {
                    let offset = layout.next(field.layout());
                    field.get_pointers_internal(base_offset + offset, add_pointer);
                }
            }
            TypeKind::Unique(_) | TypeKind::Enum { .. } => {
                self.args()[0].get_pointers_internal(base_offset, add_pointer);
            }
        }
    }

    #[inline]
    pub fn layout(&self) -> Layout {
        // TODO: Types should just store their layout directly instead of size and align
        Layout { size: self.size(), align: self.align() }
    }

    #[inline]
    pub const fn size(&self) -> usize {
        self.0.layout.size
    }

    #[inline]
    pub const fn align(&self) -> usize {
        self.0.layout.align
    }

    #[inline]
    pub const fn kind(&self) -> &TypeKind {
        &self.0.kind
    }

    #[inline]
    pub const fn args(&self) -> &[Type] {
        &self.0.args
    }
}

// @Speed: Technically, the layout doesn't need to be part of the comparisons.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TypeData {
    pub kind: TypeKind,
    pub args: Box<[Type]>,
    pub layout: Layout,
}

impl Display for TypeData {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TypeKind::CompareUnspecified => unreachable!(),
            TypeKind::Empty => write!(fmt, "()"),
            TypeKind::Float => {
                let args = &self.args[..];
                let &TypeKind::IntSize(size)   = args[1].kind() else { unreachable!() };

                let string = match size {
                    4 => "f32",
                    8 => "f64",
                    _ => unreachable!("Invalid float size: {}", size),
                };

                write!(fmt, "{}", string)
            }
            TypeKind::IntSize(v) => write!(fmt, "<int size {}>", v),
            TypeKind::IntSigned(v) => write!(fmt, "<int signed {}>", v),
            TypeKind::Int => {
                let args = &self.args[..];
                let &TypeKind::IntSigned(sign) = args[0].kind() else { unreachable!() };
                let &TypeKind::IntSize(size)   = args[1].kind() else { unreachable!() };

                let string = match (size, sign) {
                    (0, false) => "usize",
                    (0, true) => "isize",
                    (1, false) => "u8",
                    (1, true)  => "i8",
                    (2, false) => "u16",
                    (2, true)  => "i16",
                    (4, false) => "u32",
                    (4, true)  => "i32",
                    (8, false) => "u64",
                    (8, true)  => "i64",
                    _ => unreachable!("Invalid int size/align combination: {}, {}", size, sign),
                };

                write!(fmt, "{}", string)
            }
            TypeKind::Bool => write!(fmt, "bool"),
            TypeKind::Reference => write!(fmt, "&{}", self.args[0]),
            TypeKind::Buffer => write!(fmt, "[] {}", self.args[0]),
            TypeKind::Array => write!(fmt, "[{}] {}", self.args[0], self.args[1]),
            TypeKind::Function => {
                let args = &self.args[..];
                let (returns, args) = args.split_first().unwrap();

                write!(fmt, "fn(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(fmt, ", ")?;
                    }
                    write!(fmt, "{}", arg)?;
                }

                write!(fmt, ")")?;
                if !matches!(returns.kind(), TypeKind::Empty) {
                    write!(fmt, " -> {}", returns)?;
                }
                Ok(())
            }
            TypeKind::Tuple => {
                write!(fmt, "(")?;
                for (i, member) in self.args.iter().enumerate() {
                    if i > 0 {
                        write!(fmt, ", ")?;
                    }
                    write!(fmt, "{}", member)?;
                }
                write!(fmt, ")")?;
                Ok(())
            }
            TypeKind::Enum(marker, field_names) => {
                if let Some(name) = marker.name {
                    write!(fmt, "{}", name)
                } else {
                    write!(fmt, "enum {} {{ ", self.args[0])?;
                    for (i, field_name) in field_names.iter().enumerate() {
                        if i > 0 { write!(fmt, ", ")?; }
                        write!(fmt, "{}", field_name)?;
                    }
                    write!(fmt, " }}")
                }
            }
            TypeKind::Struct(names) => {
                write!(fmt, "{{")?;
                for (i, (name, member)) in names.iter().zip(&self.args[..]).enumerate() {
                    if i > 0 {
                        write!(fmt, ", ")?;
                    }
                    write!(fmt, "{}: {}", name, member)?;
                }
                write!(fmt, "}}")?;
                Ok(())
            }
            TypeKind::Unique(marker) => {
                write!(fmt, "{}({})", marker.name.map_or("<anonymous>", |v| v.as_str()), &self.args[0])
            }
            TypeKind::ConstantValue(v) => {
                write!(fmt, "<const value, {:p}", v.as_ptr())
            }
            TypeKind::Constant => {
                let type_ = &self.args[0];
                let &TypeKind::ConstantValue(value) = self.args[1].kind() else { unreachable!() };

                write!(fmt, "{}", constant_to_str(type_, value, 0))
            }
        }
    }
}

/// FIXME: I think this should be called `align_to`
pub fn to_align(value: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (value + align - 1) & !(align - 1)
}

pub use crate::type_infer::TypeKind;

impl TypeData {
    fn for_each_child(&self, mut on_inner: impl FnMut(&Type)) {
        match &self.kind {
            _ => {
                for arg in self.args.iter() {
                    on_inner(arg);
                }
            }
        }
    }

    fn calculate_size_align(&self) -> (usize, usize) {
        match &self.kind {
            TypeKind::CompareUnspecified => (0, 0),
            TypeKind::Empty => (0, 1),
            TypeKind::Reference | TypeKind::Function => (8, 8),
            TypeKind::Buffer => (16, 8),
            TypeKind::Bool => (1, 1),
            TypeKind::Unique(_) | TypeKind::Enum { .. } => self.args[0].0.calculate_size_align(),
            TypeKind::Array => {
                let internal = &self.args[0];
                let length = unsafe { self.args[1].read_constant_as_usize() };
                let member_size = internal.size();
                let align = internal.align();
                let size = array_size(member_size, align, length);
                (size, align)
            }
            TypeKind::Float => {
                let &TypeKind::IntSize(size) = self.args[0].kind() else { unreachable!() };
                debug_assert!(size == 4 || size == 8);

                (size as usize, size as usize)
            }
            TypeKind::ConstantValue(_) => (0, 1),
            TypeKind::Constant => {
                self.args[0].0.calculate_size_align()
            }
            TypeKind::IntSize(_) => (1, 1),
            TypeKind::IntSigned(_) => (1, 1),
            TypeKind::Int => {
                let &TypeKind::IntSize(mut size) = self.args[1].kind() else { unreachable!() };
                // @Cleanup: This could be better
                if size == 0 { size = 8; }
                debug_assert!(size.is_power_of_two() && size <= 8);

                (size as usize, size as usize)
            }
            TypeKind::Tuple | TypeKind::Struct(_) => {
                let members = &self.args[..];

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
        }
    }
}

#[derive(Clone, Copy, Hash, Eq, PartialEq)]
pub enum PointerInType<'a> {
    Pointer(&'a Type),
    Buffer(&'a Type),
    Function(&'a [Type]),
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
        Type::new_int(int)
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UniqueTypeMarker {
    pub loc: Location,
    pub name: Option<Ustr>,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct BufferRepr {
    pub ptr: *mut u8,
    pub length: usize,
}

fn array_size(size: usize, align: usize, num_elements: usize) -> usize {
    let element_size = to_align(size, align);
    element_size * num_elements
}
