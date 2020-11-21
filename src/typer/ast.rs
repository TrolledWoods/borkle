use crate::locals::LocalId;
use crate::location::Location;
use crate::program::MemberId;
use crate::types::Type;
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
}

impl bump_tree::MetaData for Node {
    fn validate(&self, num_args: usize) -> bool {
        matches!((&self.kind, num_args),
            (NodeKind::Constant(_), 0)
            | (NodeKind::Value(_), 0)
            | (NodeKind::FunctionCall, _)
            | (NodeKind::Block, _)
            | (NodeKind::Assign(_), 1)
            | (NodeKind::Local(_), 0)
        )
    }
}

pub enum NodeKind {
    // FIXME: The bump_tree should allow for storing buffers in the tree itself.
    // Having a vec here is fine for now though.
    Constant(Vec<u8>),
    // FIXME: `MemberId` might be a bad name here, because we also have the `Member`
    // node, and they have nothing to do with each other despite having similar names.
    Value(MemberId),
    Member(Ustr),
    FunctionCall,
    Block,
    Assign(LocalId),
    Local(LocalId),
}
