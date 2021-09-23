use crate::dependencies::DependencyList;
use crate::program::constant::ConstantRef;
use crate::typer::TypeInfo;
use crate::literal::Literal;
use crate::locals::{LabelId, LocalId, LocalVariables};
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::{BuiltinFunction, ScopeId, MemberId, MemberMetaData};
use crate::types::{Type, PtrPermits};
use std::fmt;
use std::sync::Arc;
use ustr::Ustr;

pub type NodeId = u32;

#[derive(Clone, Debug)]
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

#[derive(Clone, Debug, Default)]
pub struct AstBuilder {
    pub nodes: Vec<Node>,
}

impl AstBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    pub fn insert_root(mut self, root: Node) -> Ast {
        let root = self.add(root);

        // @Performance: This is not necessary, it's just to make sure that everything
        // is correct
        for (i, node) in self.nodes.iter().enumerate().rev().skip(1).rev() {
            if i as u32 != root && node.parent.is_none() {
                panic!("Node without a parent");
            }
        }

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

    pub fn add(&mut self, mut node: Node) -> NodeId {
        let id = self.nodes.len() as u32;

        use NodeKind::*;

        match node.kind {
            Parenthesis(inner) => self.get_mut(inner).parent = Some(id),
            Literal(_) => {},
            ArrayLiteral(ref nodes) => for &node in nodes { self.get_mut(node).parent = Some(id); },
            BuiltinFunction(_) => {},

            PolymorphicArgument(_) => {},
            ConstAtTyping {
                locals: _,
                inner,
            } => self.get_mut(inner).parent = Some(id),
            ConstAtEvaluation {
                locals: _,
                inner,
            } => self.get_mut(inner).parent = Some(id),

            Global(_, _, ref nodes) => for &node in nodes { self.get_mut(node).parent = Some(id); },
            GlobalForTyping(_, _, ref nodes) => for &node in nodes { self.get_mut(node).parent = Some(id); },

            Constant(_, _) => {},
            ResolvedGlobal(_, _) => {},

            For {
                iterator: _,
                iteration_var: _,
                iterating: condition,
                body,
                else_body,
                label: _,
            } | While {
                condition,
                iteration_var: _,
                body,
                else_body,
                label: _,
            } | If {
                condition,
                true_body: body,
                false_body: else_body,
            } => {
                self.get_mut(condition).parent = Some(id);
                self.get_mut(body).parent = Some(id);
                else_body.map(|v| self.get_mut(v).parent = Some(id));
            },
            Member {
                of,
                name: _,
            } => self.get_mut(of).parent = Some(id),

            FunctionDeclaration {
                locals: _,
                ref args,
                ref default_args,
                returns,
                body_deps: _,
                body: _,
            } => {
                for &(_, arg) in args { self.get_mut(arg).parent = Some(id); }
                for &(_, arg) in default_args { self.get_mut(arg).parent = Some(id); }
                self.get_mut(returns).parent = Some(id);
            },

            BufferType(inner)
           | TypeAsValue(inner) => self.get_mut(inner).parent = Some(id),
            NamedType {
                name: _,
                ref fields,
                aliases: _,
            } | StructType {
                ref fields,
            } => for &(_, field) in fields { self.get_mut(field).parent = Some(id); },
            ReferenceType(inner, _)
            | Reference(inner, _)
            | Defer {
                deferring: inner,
            } | BitCast {
                value: inner,
            } => {
                self.get_mut(inner).parent = Some(id);
            },
            ArrayType {
                len,
                members,
            } => {
                self.get_mut(len).parent = Some(id);
                self.get_mut(members).parent = Some(id);
            },
            FunctionType {
                ref args,
                returns,
            } => {
                self.get_mut(returns).parent = Some(id);
                for &arg in args { self.get_mut(arg).parent = Some(id); }
            },
            LiteralType(_) => {},

            Unary {
                op: _,
                operand,
            } => self.get_mut(operand).parent = Some(id),
            Binary {
                op: _,
                left,
                right,
            } => {
                self.get_mut(left).parent = Some(id);
                self.get_mut(right).parent = Some(id);
            },

            Break {
                label: _,
                num_defer_deduplications: _,
                value,
            } => self.get_mut(value).parent = Some(id),


            FunctionCall {
                calling,
                ref args,
                ref named_args,
            } => {
                self.get_mut(calling).parent = Some(id);
                for &arg in args { self.get_mut(arg).parent = Some(id); }
                for &(_, arg) in named_args { self.get_mut(arg).parent = Some(id); }
            },
            ResolvedFunctionCall {
                calling,
                ref args,
            } => {
                self.get_mut(calling).parent = Some(id);
                for &(_, arg) in args { self.get_mut(arg).parent = Some(id); }
            },

            Block {
                ref contents,
                label: _,
            } => for &arg in contents { self.get_mut(arg).parent = Some(id); },
            Empty | Uninit | Zeroed => {},

            TypeBound {
                value,
                bound,
            } => {
                self.get_mut(value).parent = Some(id);
                self.get_mut(bound).parent = Some(id);
            },
            Declare {
                local: _,
                value,
            } => self.get_mut(value).parent = Some(id),
            Local(_) => {},

            ArrayToBuffer {
                length: _,
                array,
            } => {
                self.get_mut(array).parent = Some(id);
            },
            BufferToVoid {
                buffer,
                inner: _,
            } => {
                self.get_mut(buffer).parent = Some(id);
            },
            VoidToBuffer {
                any,
                inner: _,
            } => {
                self.get_mut(any).parent = Some(id);
            },
            PtrToAny {
                ptr,
                type_: _,
            } => {
                self.get_mut(ptr).parent = Some(id);
            },
        }

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

#[derive(Clone)]
pub struct Node {
    pub loc: Location,
    pub kind: NodeKind,
    pub parent: Option<NodeId>,
    pub type_: TypeInfo,
}

impl Node {
    pub const fn new(loc: Location, kind: NodeKind) -> Self {
        Self { loc, kind, type_: TypeInfo::None, parent: None }
    }

    pub fn type_(&self) -> Type {
        if let TypeInfo::Resolved(type_) = self.type_ {
            type_
        } else {
            unreachable!("Called type_ on Node before typing was completed");
        }
    }
}

#[derive(Debug, Clone)]
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

    Global(ScopeId, Ustr, Vec<NodeId>),
    GlobalForTyping(ScopeId, Ustr, Vec<NodeId>),

    Constant(ConstantRef, Option<Arc<MemberMetaData>>),
    ResolvedGlobal(MemberId, Arc<MemberMetaData>),

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
    ResolvedFunctionCall {
        calling: NodeId,
        args: Vec<(usize, NodeId)>,
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

    ArrayToBuffer {
        length: usize,
        array: NodeId,
    },
    BufferToVoid {
        buffer: NodeId,
        inner: Type,
    },
    VoidToBuffer {
        any: NodeId,
        inner: Type,
    },
    PtrToAny {
        ptr: NodeId,
        type_: Type,
    },
}

impl fmt::Debug for Node {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(fmt)
    }
}
