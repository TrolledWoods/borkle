use crate::literal::Literal;
use crate::locals::LocalId;
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::types::Type;
use std::fmt;
use ustr::Ustr;

#[derive(Clone)]
pub struct Node {
    pub loc: Location,
    pub kind: NodeKind,
}

impl Node {
    pub const fn new(loc: Location, kind: NodeKind) -> Self {
        Self { loc, kind }
    }
}

#[derive(Debug, Clone)]
pub enum NodeKind {
    Literal(Literal),
    Global(Ustr),
    Extern {
        library_name: String,
        symbol_name: String,
    },

    Member(Ustr),

    LiteralType(Type),

    Unary(UnaryOp),
    Binary(BinaryOp),

    FunctionCall,
    Block,
    Empty,

    TypeBound,
    Declare(LocalId),
    Local(LocalId),
}

impl fmt::Debug for Node {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(fmt)
    }
}

impl bump_tree::MetaData for Node {
    fn validate(&self, num_args: usize) -> bool {
        matches!(
            (&self.kind, num_args),

              (NodeKind::Literal(_),     0)
            | (NodeKind::LiteralType(_), 0)
            | (NodeKind::Global(_),      0)
            | (NodeKind::Local(_),       0)
            | (NodeKind::Member(_),      1)
            | (NodeKind::Unary(_),       1)
            | (NodeKind::Declare(_),     1)
            | (NodeKind::Binary(_),      2)
            | (NodeKind::Extern { .. },  0)
            | (NodeKind::TypeBound,      2)
            | (NodeKind::Empty,          0)
            | (NodeKind::FunctionCall,   1..=usize::MAX)
            | (NodeKind::Block,          _)
        )
    }
}
