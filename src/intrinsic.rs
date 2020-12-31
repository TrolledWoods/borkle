use crate::types::{type_creation::*, Type};
use std::fmt;

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
    i_stdout_write
        [buf_type(u8_type())]
        usize_type(),
    i_stdout_flush
        []
        empty_type(),
    i_stdin_getline
        []
        buf_type(u8_type()),
    i_alloc
        [usize_type()]
        any_type(),
    i_dealloc
        [any_buf_type()]
        empty_type(),
    i_copy
        [any_type(), any_type(), usize_type()]
        empty_type(),
    i_copy_nonoverlapping
        [any_type(), any_type(), usize_type()]
        empty_type(),
}

impl fmt::Display for Intrinsic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
