pub trait Operator: Sized {
    fn from_prefix(string: &str) -> Option<(Self, &'_ str)>;
}

macro_rules! operator {
    ($enum_name:ident {
        $(
            $operator_name:ident = ($name:literal, $precedence:literal),
        )*
    }) => {
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        pub enum $enum_name {
            $($operator_name,)*
        }

        impl $enum_name {
            #[allow(unused)]
            pub const fn precedence(&self) -> usize {
                match self {
                    $(Self::$operator_name => $precedence,)*
                }
            }
        }

        impl Operator for $enum_name {
            fn from_prefix(string: &str) -> Option<(Self, &'_ str)> {
                $(if let Some(suffix) = string.strip_prefix($name) {
                    return Some((Self::$operator_name, suffix));
                })*

                None
            }
        }
    };
}

operator!(UnaryOp {
    Negate = ("-", 0),
    Not = ("!", 0),
    Reference = ("&", 0),
    Dereference = ("*", 0),
});

operator!(BinaryOp {
    And = ("&&", 1),
    Or  = ("||", 2),
    Equals = ("==", 3),

    Add = ("+", 100),
    Sub = ("-", 100),
    Mult = ("*", 101),
    Div = ("/", 102),
    BitAnd = ("&", 4),
    BitOr = ("|", 5),
});

operator!(AccessOp {
    Member = (".", 0),
});
