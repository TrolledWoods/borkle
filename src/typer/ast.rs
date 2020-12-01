use crate::locals::{LocalId, LocalVariables};
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::MemberId;
use crate::types::Type;
use std::fmt::{self, Debug};
use ustr::Ustr;

pub struct Node {
    // loc: Location,
    type_: Type,
    kind: NodeKind,
}

impl Node {
    pub fn new<T>(_loc: Location, kind: NodeKind, type_: T) -> Self
    where
        T: Into<Type>,
    {
        Self {
            // loc,
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
            NodeKind::Uninit | NodeKind::Constant(_) | NodeKind::Global(_) | NodeKind::Local(_) => {
                num_args == 0
            }
            NodeKind::FunctionCall { .. } => true,
            NodeKind::Block => num_args > 0,
            NodeKind::FunctionDeclaration { locals: _ }
            | NodeKind::BitCast
            | NodeKind::Member(_)
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

impl<'a> From<&'a [u8]> for ByteArray {
    fn from(other: &'a [u8]) -> Self {
        Self(other.into())
    }
}

impl From<u64> for ByteArray {
    fn from(other: u64) -> Self {
        Self(other.to_le_bytes().into())
    }
}

impl From<unsafe extern "C" fn()> for ByteArray {
    fn from(other: unsafe extern "C" fn()) -> Self {
        (other as usize).into()
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
    // FIXME: This should be the 'Member' struct from the types, not a string.
    Member(Ustr),
    FunctionCall { is_extern: bool },
    FunctionDeclaration { locals: LocalVariables },
    Block,

    While,
    If { has_else: bool },

    Uninit,
    Assign,
    Local(LocalId),
    Declare(LocalId),

    Binary(BinaryOp),
    Unary(UnaryOp),

    BitCast,
}

impl Debug for Node {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}: ", self.type_)?;
        self.kind.fmt(fmt)?;
        Ok(())
    }
}
