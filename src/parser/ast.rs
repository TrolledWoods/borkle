use crate::locals::LocalId;
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use std::fmt;
use ustr::Ustr;

#[derive(Clone)]
pub struct Node {
    pub loc: Location,
    pub kind: NodeKind,
}

impl Node {
    pub fn new(loc: Location, kind: NodeKind) -> Self {
        Node { loc, kind }
    }
}

#[derive(Clone)]
pub enum NodeKind {
    Int(u64),
    Member(Ustr),
    Unary(UnaryOp),
    Binary(BinaryOp),
    FunctionCall,
    Block,
    Empty,
    Declare(LocalId),
    Local(LocalId),
}

impl fmt::Debug for Node {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(fmt)
    }
}

impl fmt::Debug for NodeKind {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(num) => write!(fmt, "{}", num),
            Self::Member(name) => write!(fmt, "member {}", name),
            Self::Unary(op) => write!(fmt, "{:?}", op),
            Self::Binary(op) => write!(fmt, "{:?}", op),
            Self::FunctionCall => write!(fmt, "Function call"),
            Self::Block => write!(fmt, "Block"),
            Self::Empty => write!(fmt, "()"),

            Self::Declare(id) => write!(fmt, "Decl {:?}", id),
            Self::Local(id) => write!(fmt, "{:?}", id),
        }
    }
}

impl bump_tree::MetaData for Node {
    fn validate(&self, num_args: usize) -> bool {
        matches!(
            (&self.kind, num_args),

              (NodeKind::Local(_),     0)
            | (NodeKind::Int(_),       0)
            | (NodeKind::Member(_),    1)
            | (NodeKind::Unary(_),     1)
            | (NodeKind::Binary(_),    2)
            | (NodeKind::Empty,        0)
            | (NodeKind::Declare(_),   0..=1)
            | (NodeKind::FunctionCall, 1..=usize::MAX)
            | (NodeKind::Block,        _)
        )
    }
}
