use crate::dependencies::DependencyList;
use crate::literal::Literal;
use crate::locals::{LabelId, LocalId, LocalVariables};
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::{BuiltinFunction, ScopeId};
use crate::types::{Type, PtrPermits};
use std::fmt;
use std::sync::Arc;
use ustr::Ustr;

pub type NodeId = u32;

#[derive(Debug)]
pub struct Ast {
    builder: AstBuilder,
    pub root: NodeId,
}

impl std::ops::Deref for Ast {
    type Target = AstBuilder;

    fn deref(&self) -> &Self::Target {
        &self.builder
    }
}

impl std::ops::DerefMut for Ast {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.builder
    }
}

#[derive(Debug, Default)]
pub struct AstBuilder {
    pub nodes: Vec<Node>,
}

impl AstBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert_root(mut self, root: Node) -> Ast {
        let root = self.add(root);
        Ast {
            builder: self,
            root,
        }
    }

    pub fn get(&self, id: NodeId) -> &Node {
        let id = id as usize;
        debug_assert!(id < self.nodes.len());
        unsafe {
            self.nodes.get_unchecked(id)
        }
    }

    pub fn get_mut(&mut self, id: NodeId) -> &mut Node {
        let id = id as usize;
        debug_assert!(id < self.nodes.len());
        unsafe {
            self.nodes.get_unchecked_mut(id)
        }
    }

    pub fn add(&mut self, node: Node) -> NodeId {
        let id = self.nodes.len() as u32;
        self.nodes.push(node);
        id
    }

    /*pub fn has_to_be_alone(&self, id: NodeId) -> bool {
        match self.get(id).kind {
            NodeKind::ConstAtTyping { .. }
            | NodeKind::ConstAtEvaluation { .. }
            | NodeKind::If { .. }
            | NodeKind::For { .. }
            | NodeKind::While { .. } => true,
            NodeKind::BitCast {
                value: operand, ..
            }
            | NodeKind::Unary { operand, .. } => self.has_to_be_alone(operand),
            _ => false,
        }
    }*/
}

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
    ArrayLiteral(Vec<NodeId>),
    BuiltinFunction(BuiltinFunction),

    PolymorphicArgument(usize),
    ConstAtTyping {
        locals: LocalVariables,
        inner: NodeId,
    },
    ConstAtEvaluation {
        locals: LocalVariables,
        inner: NodeId,
    },

    // FIXME: Performance; Put the vector in the self buffer as well, since that should totally be
    // possible to do.
    Global(ScopeId, Ustr, Vec<NodeId>),
    GlobalForTyping(ScopeId, Ustr, Vec<NodeId>),

    For {
        iterator: LocalId,
        iteration_var: LocalId,
        iterating: NodeId,
        body: NodeId,
        else_body: Option<NodeId>,
        label: LabelId,
    },
    While {
        condition: NodeId,
        iteration_var: LocalId,
        body: NodeId,
        else_body: Option<NodeId>,
        label: LabelId,
    },
    If {
        condition: NodeId,
        true_body: NodeId,
        false_body: Option<NodeId>,
    },

    Member {
        of: NodeId,
        name: Ustr,
    },

    FunctionDeclaration {
        locals: LocalVariables,
        args: Vec<(Ustr, NodeId)>,
        default_args: Vec<(Ustr, NodeId)>,
        returns: NodeId,
        body_deps: DependencyList,
        body: Arc<Ast>,
    },

    TypeAsValue(NodeId),
    NamedType {
        name: Ustr,
        fields: Vec<(Ustr, NodeId)>,
        aliases: Vec<(Ustr, Vec<(Location, Ustr)>)>,
    },
    StructType {
        fields: Vec<(Ustr, NodeId)>,
    },
    BufferType(NodeId),
    ArrayType {
        len: NodeId,
        members: NodeId,
    },
    FunctionType {
        args: Vec<NodeId>,
        returns: NodeId,
    },
    ReferenceType(NodeId, PtrPermits),
    LiteralType(Type),

    Reference(NodeId, PtrPermits),
    Unary {
        op: UnaryOp,
        operand: NodeId,
    },
    Binary {
        op: BinaryOp,
        left: NodeId,
        right: NodeId,
    },

    Break {
        label: LabelId,
        num_defer_deduplications: usize,
        value: NodeId,
    },

    Defer {
        deferring: NodeId,
    },

    FunctionCall {
        calling: NodeId,
        args: Vec<NodeId>,
        named_args: Vec<(Ustr, NodeId)>,
    },
    Block {
        contents: Vec<NodeId>,
        label: Option<LabelId>,
    },
    Parenthesis(NodeId),
    Empty,
    Uninit,
    Zeroed,

    TypeBound {
        value: NodeId,
        bound: NodeId,
    },
    BitCast {
        value: NodeId,
    },

    Declare {
        local: LocalId,
        value: NodeId,
    },
    Local(LocalId),
}

impl fmt::Debug for Node {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(fmt)
    }
}
