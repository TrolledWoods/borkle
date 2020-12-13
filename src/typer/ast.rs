use crate::locals::{LocalId, LocalVariables};
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::constant::ConstantRef;
use crate::program::{MemberId, MemberMetaData};
use crate::self_buffer::SelfBox;
use crate::types::Type;
use std::fmt::{self, Debug};
use std::sync::Arc;
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

#[derive(Debug)]
pub enum NodeKind {
    ConstAtEvaluation {
        locals: LocalVariables,
        inner: SelfBox<Node>,
    },
    Constant(ConstantRef),
    Global(MemberId, Arc<MemberMetaData>),
    // FIXME: This should be the 'Member' struct from the types, not a string.
    Member {
        name: Ustr,
        of: SelfBox<Node>,
    },
    FunctionCall {
        is_extern: bool,
        calling: SelfBox<Node>,
        args: Vec<SelfBox<Node>>,
    },
    FunctionDeclaration {
        locals: LocalVariables,
        arg_names: Vec<Ustr>,
        body: SelfBox<Node>,
    },
    Break {
        label: crate::locals::LabelId,
        num_defer_deduplications: usize,
        value: SelfBox<Node>,
    },

    Defer {
        deferred: SelfBox<Node>,
    },
    Block {
        label: Option<crate::locals::LabelId>,
        contents: Vec<SelfBox<Node>>,
    },

    While {
        condition: SelfBox<Node>,
        body: SelfBox<Node>,
    },
    If {
        condition: SelfBox<Node>,
        true_body: SelfBox<Node>,
        false_body: Option<SelfBox<Node>>,
    },

    Uninit,
    Assign {
        lvalue: SelfBox<Node>,
        rvalue: SelfBox<Node>,
    },
    Local(LocalId),
    Declare {
        local: LocalId,
        value: SelfBox<Node>,
    },

    ArrayLiteral {
        elements: Vec<SelfBox<Node>>,
    },

    Binary {
        op: BinaryOp,
        left: SelfBox<Node>,
        right: SelfBox<Node>,
    },
    Unary {
        op: UnaryOp,
        operand: SelfBox<Node>,
    },

    BitCast {
        value: SelfBox<Node>,
    },
    ArrayToBuffer {
        length: usize,
        array: SelfBox<Node>,
    },
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
