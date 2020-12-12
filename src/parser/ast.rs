use crate::literal::Literal;
use crate::locals::{LabelId, LocalId, LocalVariables};
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::self_buffer::SelfBox;
use crate::types::Type;
use std::fmt;
use std::path::PathBuf;
use ustr::Ustr;

pub struct Node {
    pub loc: Location,
    pub kind: NodeKind,
}

impl Node {
    pub const fn new(loc: Location, kind: NodeKind) -> Self {
        Self { loc, kind }
    }
}

#[derive(Debug)]
pub enum NodeKind {
    Literal(Literal),
    ArrayLiteral(Vec<SelfBox<Node>>),

    ConstAtTyping {
        locals: LocalVariables,
        inner: SelfBox<Node>,
    },

    Global(Ustr),
    GlobalForTyping(Ustr),
    Extern {
        library_name: PathBuf,
        symbol_name: String,
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

    Member {
        of: SelfBox<Node>,
        name: Ustr,
    },

    FunctionDeclaration {
        locals: LocalVariables,
        args: Vec<SelfBox<Node>>,
        returns: SelfBox<Node>,
        body: SelfBox<Node>,
    },

    TypeAsValue(SelfBox<Node>),
    StructType {
        fields: Vec<(Ustr, SelfBox<Node>)>,
    },
    BufferType(SelfBox<Node>),
    ArrayType {
        len: SelfBox<Node>,
        members: SelfBox<Node>,
    },
    FunctionType {
        is_extern: bool,
        args: Vec<SelfBox<Node>>,
        returns: SelfBox<Node>,
    },
    ReferenceType(SelfBox<Node>),
    LiteralType(Type),

    Unary {
        op: UnaryOp,
        operand: SelfBox<Node>,
    },
    Binary {
        op: BinaryOp,
        left: SelfBox<Node>,
        right: SelfBox<Node>,
    },

    Break {
        label: LabelId,
        num_defer_deduplications: usize,
        value: SelfBox<Node>,
    },

    Defer {
        deferring: SelfBox<Node>,
    },

    FunctionCall {
        calling: SelfBox<Node>,
        args: Vec<SelfBox<Node>>,
    },
    Block {
        contents: Vec<SelfBox<Node>>,
        label: Option<LabelId>,
    },
    Empty,
    Uninit,

    TypeBound {
        value: SelfBox<Node>,
        bound: SelfBox<Node>,
    },
    BitCast {
        value: SelfBox<Node>,
    },

    Declare {
        local: LocalId,
        value: SelfBox<Node>,
    },
    Assign {
        lvalue: SelfBox<Node>,
        rvalue: SelfBox<Node>,
    },
    Local(LocalId),
}

impl fmt::Debug for Node {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(fmt)
    }
}
