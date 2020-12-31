use std::fmt;

macro_rules! create_intrinsics {
    ($($name:ident),*,) => {
        #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
        #[repr(u64)]
        #[allow(non_camel_case_types)]
        pub enum Intrinsic {
            $($name),*
        }

        impl Intrinsic {
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
    i_stdout_write,
    i_stdin_read,
    i_alloc,
    i_dealloc,
}

impl fmt::Display for Intrinsic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
