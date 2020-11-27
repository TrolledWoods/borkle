use crate::literal::Literal;
use crate::locals::{LocalId, LocalVariables};
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

    FunctionDeclaration {
        locals: LocalVariables,
    },

    FunctionType {
        is_extern: bool,
    },
    ReferenceType,
    LiteralType(Type),

    Unary(UnaryOp),
    Binary(BinaryOp),

    FunctionCall,
    Block,
    Empty,
    Uninit,

    TypeBound,
    BitCast,

    Declare(LocalId),
    Assign,
    Local(LocalId),
}

impl fmt::Debug for Node {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(fmt)
    }
}

impl bump_tree::MetaData for Node {
    fn validate(&self, num_args: usize) -> bool {
        match self.kind {
            NodeKind::Local(_)
            | NodeKind::Empty
            | NodeKind::Literal(_)
            | NodeKind::Global(_)
            | NodeKind::Extern { .. }
            | NodeKind::Uninit
            | NodeKind::LiteralType(_) => num_args == 0,
            NodeKind::Declare(_)
            | NodeKind::BitCast
            | NodeKind::Member(_)
            | NodeKind::ReferenceType
            | NodeKind::Unary(_) => num_args == 1,
            NodeKind::Assign | NodeKind::Binary(_) | NodeKind::TypeBound => num_args == 2,
            NodeKind::FunctionDeclaration { locals: _ } => num_args >= 2,
            NodeKind::Block | NodeKind::FunctionCall | NodeKind::FunctionType { is_extern: _ } => {
                num_args >= 1
            }
        }
    }
}
