use crate::dependencies::DependencyList;
use crate::literal::Literal;
use crate::locals::{LabelId, LocalId, LocalVariables};
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::{BuiltinFunction, ScopeId};
use crate::self_buffer::{SelfBox, SelfTree};
use crate::types::Type;
use std::fmt;
use std::sync::Arc;
use ustr::Ustr;

pub struct Node {
    pub loc: Location,
    pub kind: NodeKind,
}

impl Node {
    pub const fn new(loc: Location, kind: NodeKind) -> Self {
        Self { loc, kind }
    }

    pub fn has_to_be_alone(&self) -> bool {
        match self.kind {
            NodeKind::ConstAtTyping { .. }
            | NodeKind::ConstAtEvaluation { .. }
            | NodeKind::If { .. }
            | NodeKind::For { .. }
            | NodeKind::While { .. } => true,
            NodeKind::BitCast {
                value: ref operand, ..
            }
            | NodeKind::Unary { ref operand, .. } => operand.has_to_be_alone(),
            _ => false,
        }
    }
}

#[derive(Debug)]
pub enum NodeKind {
    Literal(Literal),
    ArrayLiteral(Vec<SelfBox<Node>>),
    BuiltinFunction(BuiltinFunction),

    PolymorphicArgument(usize),
    ConstAtTyping {
        locals: LocalVariables,
        inner: SelfBox<Node>,
    },
    ConstAtEvaluation {
        locals: LocalVariables,
        inner: SelfBox<Node>,
    },

    // FIXME: Performance; Put the vector in the self buffer as well, since that should totally be
    // possible to do.
    Global(ScopeId, Ustr, Vec<SelfBox<Node>>),
    GlobalForTyping(ScopeId, Ustr, Vec<SelfBox<Node>>),

    For {
        iterator: LocalId,
        iteration_var: LocalId,
        iterating: SelfBox<Node>,
        body: SelfBox<Node>,
        else_body: Option<SelfBox<Node>>,
        label: LabelId,
    },
    While {
        condition: SelfBox<Node>,
        iteration_var: LocalId,
        body: SelfBox<Node>,
        else_body: Option<SelfBox<Node>>,
        label: LabelId,
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
        args: Vec<(Ustr, SelfBox<Node>)>,
        default_args: Vec<(Ustr, SelfBox<Node>)>,
        returns: SelfBox<Node>,
        body_deps: DependencyList,
        body: Arc<SelfTree<Node>>,
    },

    TypeAsValue(SelfBox<Node>),
    NamedType {
        name: Ustr,
        fields: Vec<(Ustr, SelfBox<Node>)>,
        aliases: Vec<(Ustr, Vec<(Location, Ustr)>)>,
    },
    StructType {
        fields: Vec<(Ustr, SelfBox<Node>)>,
    },
    BufferType(SelfBox<Node>),
    ArrayType {
        len: SelfBox<Node>,
        members: SelfBox<Node>,
    },
    FunctionType {
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
        named_args: Vec<(Ustr, SelfBox<Node>)>,
    },
    Block {
        contents: Vec<SelfBox<Node>>,
        label: Option<LabelId>,
    },
    Parenthesis(SelfBox<Node>),
    Empty,
    Uninit,
    Zeroed,

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
