use crate::locals::{LocalId, LocalVariables};
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::constant::ConstantRef;
use crate::program::MemberId;
use crate::types::Type;
use std::fmt::{self, Debug};
use ustr::Ustr;

pub struct Node {
    pub loc: Location,
    type_: Type,
    kind: NodeKind,
}

impl Node {
    pub fn new<T>(loc: Location, kind: NodeKind, type_: T) -> Self
    where
        T: Into<Type>,
    {
        Self {
            loc,
            kind,
            type_: type_.into(),
        }
    }

    pub fn kind(&self) -> &'_ NodeKind {
        &self.kind
    }

    pub fn type_(&self) -> Type {
        self.type_
    }
}

impl bump_tree::MetaData for Node {
    fn validate(&self, num_args: usize) -> bool {
        match self.kind {
            NodeKind::Defer(_)
            | NodeKind::Uninit
            | NodeKind::Constant(_)
            | NodeKind::Global(_)
            | NodeKind::Local(_) => num_args == 0,
            NodeKind::FunctionCall { .. } => true,
            NodeKind::Block { .. } => num_args > 0,
            NodeKind::FunctionDeclaration { locals: _ }
            | NodeKind::BitCast
            | NodeKind::ArrayToBuffer(_)
            | NodeKind::Member(_)
            | NodeKind::Break(_, _)
            | NodeKind::Declare(_)
            | NodeKind::Unary(_) => num_args == 1,
            NodeKind::While | NodeKind::Assign | NodeKind::Binary(_) => num_args == 2,
            NodeKind::If { has_else } => {
                if has_else {
                    num_args == 3
                } else {
                    num_args == 2
                }
            }
            NodeKind::ArrayLiteral(len) => num_args == len,
        }
    }
}

#[derive(Debug)]
pub enum NodeKind {
    Constant(ConstantRef),
    // FIXME: `MemberId` might be a bad name here, because we also have the `Member`
    // node, and they have nothing to do with each other despite having similar names.
    Global(MemberId),
    // FIXME: This should be the 'Member' struct from the types, not a string.
    Member(Ustr),
    FunctionCall {
        is_extern: bool,
    },
    FunctionDeclaration {
        locals: LocalVariables,
    },
    Break(crate::locals::LabelId, usize),

    Defer(Box<super::Ast>),
    Block {
        label: Option<crate::locals::LabelId>,
    },

    While,
    If {
        has_else: bool,
    },

    Uninit,
    Assign,
    Local(LocalId),
    Declare(LocalId),

    ArrayLiteral(usize),

    Binary(BinaryOp),
    Unary(UnaryOp),

    BitCast,
    ArrayToBuffer(usize),
}

unsafe impl Send for NodeKind {}
unsafe impl Sync for NodeKind {}

impl Debug for Node {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}: ", self.type_)?;
        self.kind.fmt(fmt)?;
        Ok(())
    }
}
