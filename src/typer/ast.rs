use crate::locals::LocalId;
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::MemberId;
use crate::types::Type;
use std::fmt::{self, Debug};
use ustr::Ustr;

pub struct Node {
    loc: Location,
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
            NodeKind::Constant(_) | NodeKind::Global(_) | NodeKind::Local(_) => num_args == 0,
            NodeKind::FunctionCall => true,
            NodeKind::Block => num_args > 0,
            NodeKind::Member(_) | NodeKind::Assign(_) | NodeKind::Unary(_) => num_args == 1,
            NodeKind::Binary(_) => num_args == 2,
        }
    }
}

pub struct ByteArray(pub Vec<u8>);

impl Debug for ByteArray {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, byte) in self.0.iter().enumerate() {
            if i > 0 {
                write!(fmt, " ")?;
            }

            write!(fmt, "{:X}", byte)?;
        }

        Ok(())
    }
}

impl From<u64> for ByteArray {
    fn from(other: u64) -> Self {
        Self(other.to_le_bytes().into())
    }
}

impl From<usize> for ByteArray {
    fn from(other: usize) -> Self {
        Self(other.to_le_bytes().into())
    }
}

impl From<u8> for ByteArray {
    fn from(other: u8) -> Self {
        Self(vec![other])
    }
}

impl From<()> for ByteArray {
    fn from(_: ()) -> Self {
        Self(vec![])
    }
}

#[derive(Debug)]
pub enum NodeKind {
    // FIXME: The bump_tree should allow for storing buffers in the tree itself.
    // Having a vec here is fine for now though.
    Constant(ByteArray),
    // FIXME: `MemberId` might be a bad name here, because we also have the `Member`
    // node, and they have nothing to do with each other despite having similar names.
    Global(MemberId),
    Member(Ustr),
    FunctionCall,
    Block,

    // TODO: Assign should have 2 children, one being an lvalue, rather than having a LocalId like
    // this.
    Assign(LocalId),
    Local(LocalId),

    Binary(BinaryOp),
    Unary(UnaryOp),
}

impl Debug for Node {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}: ", self.type_)?;
        self.kind.fmt(fmt)?;
        Ok(())
    }
}
