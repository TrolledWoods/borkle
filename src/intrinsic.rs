use crate::types::{IntTypeKind, Type, TypeKind};
use std::fmt;
use ustr::Ustr;

macro_rules! create_intrinsics {
    ($($name:ident [$($arg_type:expr),*] $return_type:expr),*,) => {
        #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
        #[repr(u64)]
        #[allow(non_camel_case_types)]
        pub enum Intrinsic {
            $($name),*
        }

        impl Intrinsic {
            pub fn get_function_data(self) -> (Vec<Type>, Type) {
                match self {
                    $(
                        Self::$name => (
                            vec![$($arg_type),*],
                            $return_type,
                        ),
                    )*
                }
            }

            pub fn from_string(string: &str) -> Option<Self> {
                match string {
                    $(
                        stringify!($name) => Some(Self::$name),
                    )*
                    _ => None,
                }
            }

            pub fn as_str(self) -> &'static str {
                match self {
                    $(
                        Self::$name => stringify!($name),
                    )*
                }
            }
        }
    }
}

create_intrinsics! {
    i_add_u64
        [Type::new(TypeKind::Int(IntTypeKind::U64)), Type::new(TypeKind::Int(IntTypeKind::U64))]
        Type::new(TypeKind::Int(IntTypeKind::U64)),
    // i_stdin_read
    //     [Type::new(TypeKind::Buffer(Type::new(TypeKind::Int(IntTypeKind::U8))))]
    //     Type::new(TypeKind::Int(IntTypeKind::Usize)),
    // i_alloc
    //     [Type::new(TypeKind::Buffer(Type::new(TypeKind::Int(IntTypeKind::U8))))]
    //     Type::new(TypeKind::Int(IntTypeKind::Usize)),
    // i_dealloc
    //     [Type::new(TypeKind::Buffer(Type::new(TypeKind::Int(IntTypeKind::U8))))]
    //     Type::new(TypeKind::Int(IntTypeKind::Usize)),
}

impl fmt::Display for Intrinsic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
