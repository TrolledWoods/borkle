use crate::locals::LocalId;
use crate::location::Location;
use crate::tree;
use std::fmt;

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
            Self::FunctionCall => write!(fmt, "Function call"),
            Self::Block => write!(fmt, "Block"),
            Self::Empty => write!(fmt, "()"),

            Self::Declare(id) => write!(fmt, "Decl {:?}", id),
            Self::Local(id) => write!(fmt, "{:?}", id),
        }
    }
}

impl tree::MetaData for Node {
    fn validate(&self, num_args: usize) -> bool {
        matches!(
            (&self.kind, num_args),

              (NodeKind::Local(_),     0)
            | (NodeKind::Int(_),       0)
            | (NodeKind::Empty,        0)
            | (NodeKind::Declare(_),   0..=1)
            | (NodeKind::FunctionCall, 1..=usize::MAX)
            | (NodeKind::Block,        _)
        )
    }
}
