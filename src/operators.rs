#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum UnaryOp {
    Negate,
    Not,
    Reference,
    Dereference,
}

const UNARY_OP_STRINGS: &[(&str, UnaryOp)] = &[
    ("-", UnaryOp::Negate),
    ("!", UnaryOp::Not),
    ("&", UnaryOp::Reference),
    ("*", UnaryOp::Dereference),
];

impl UnaryOp {
    /// Tries to find this operator in the prefix of a string.
    /// If it does find it, it returns the operator as well
    /// as the rest of the string that wasn't part of the operator.
    pub fn from_prefix(string: &str) -> Option<(Self, &'_ str)> {
        for &(prefix, operator) in UNARY_OP_STRINGS {
            if let Some(suffix) = string.strip_prefix(prefix) {
                return Some((operator, suffix));
            }
        }

        None
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BinaryOp {
    And,
    Or,
    Equals,

    Add,
    Sub,
    BitAnd,
    BitOr,
}

const BINARY_OP_STRINGS: &[(&str, BinaryOp)] = &[
    ("&&", BinaryOp::And),
    ("||", BinaryOp::Or),
    ("==", BinaryOp::Equals),
    ("+", BinaryOp::Add),
    ("-", BinaryOp::Add),
    ("&", BinaryOp::BitAnd),
    ("|", BinaryOp::BitOr),
];

impl BinaryOp {
    /// Tries to find this operator in the prefix of a string.
    /// If it does find it, it returns the operator as well
    /// as the rest of the string that wasn't part of the operator.
    pub fn from_prefix(string: &str) -> Option<(Self, &'_ str)> {
        for &(prefix, operator) in BINARY_OP_STRINGS {
            if let Some(suffix) = string.strip_prefix(prefix) {
                return Some((operator, suffix));
            }
        }

        None
    }
}
