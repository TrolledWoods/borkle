use crate::types::{IntTypeKind, Type, TypeKind};

pub trait Operator: Sized {
    fn from_prefix(string: &str) -> Option<(Self, &'_ str)>;
    fn precedence(&self) -> usize;
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

        impl Operator for $enum_name {
            fn from_prefix(string: &str) -> Option<(Self, &'_ str)> {
                $(if let Some(suffix) = string.strip_prefix($name) {
                    return Some((Self::$operator_name, suffix));
                })*

                None
            }

            fn precedence(&self) -> usize {
                match self {
                    $(Self::$operator_name => $precedence,)*
                }
            }
        }
    };
}

operator!(UnaryOp {
    Negate = ("-", 0),
    Not = ("!", 0),
    Reference = ("&", 0),
    Dereference = ("*", 0),
    Member = (".", 0),
});

operator!(BinaryOp {
    TypeBound = (":", 9),

    And = ("&&", 6),
    Or  = ("||", 6),
    Range = ("..", 48539),

    ShiftLeft = ("<<", 99),
    ShiftRight = (">>", 99),

    Equals = ("==", 8),
    NotEquals = ("!=", 8),
    LargerThanEquals = (">=", 8),
    LargerThan = (">", 8),
    LessThanEquals = ("<=", 8),
    LessThan = ("<", 8),

    Add = ("+", 100),
    Sub = ("-", 100),
    Mult = ("*", 101),
    Div = ("/", 101),
    Modulo = ("%", 101),
    BitAnd = ("&", 7),
    BitOr = ("|", 7),

    Is = ("is", 3),

    Assign = ("=", 1),
});

operator!(AccessOp {
    Member = (".", 0),
});

impl BinaryOp {
    pub fn is_right_to_left(self) -> bool {
        matches!(self, BinaryOp::Assign)
    }
}
