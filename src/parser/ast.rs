use crate::dependencies::DependencyList;
use crate::program::constant::ConstantRef;
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

    pub fn set_root(mut self, root: NodeId) -> Ast {
        // @Performance: This is not necessary, it's just to make sure that everything
        // is correct
        for (i, node) in self.nodes.iter().enumerate().rev().skip(1).rev() {
            if i as u32 != root && node.parent.is_none() {
                panic!("Node without a parent {:?}", node);
            }
        }

        Ast {
            builder: self,
            root,
        }
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

    pub fn add(&mut self, node: Node) -> NodeId {
        let id = self.nodes.len() as u32;

        use NodeKind::*;

        match node.kind {
            Parenthesis(inner) => self.get_mut(inner).parent = Some(id),
            Literal(_) => {},
            ArrayLiteral(ref nodes) => for &node in nodes { self.get_mut(node).parent = Some(id); },
            BuiltinFunction(_) => {},

            PolymorphicArgument(_) => {},
            ConstAtTyping {
                inner,
            } => self.get_mut(inner).parent = Some(id),
            ConstAtEvaluation {
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
                ref args,
                returns,
                body,
            } => {
                for &(_, arg) in args { self.get_mut(arg).parent = Some(id); }
                self.get_mut(returns).parent = Some(id);
                self.get_mut(body).parent = Some(id);
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
            | Reference(inner)
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
            LiteralType(_) | ImplicitType => {},

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
            } => {
                self.get_mut(calling).parent = Some(id);
                for &arg in args { self.get_mut(arg).parent = Some(id); }
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
                dummy_local_node,
                value,
            } => {
                self.get_mut(value).parent = Some(id);
                self.get_mut(dummy_local_node).parent = Some(id);
            }
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
    pub type_infer_value_id: crate::type_infer::ValueId,
    pub type_: Option<Type>,
}

impl Node {
    pub const fn new(loc: Location, kind: NodeKind) -> Self {
        Self { loc, kind, type_: None, parent: None, type_infer_value_id: 0xffff_ffff }
    }

    pub fn type_(&self) -> Type {
        self.type_.unwrap()
    }
}

#[derive(Debug, Clone)]
pub enum NodeKind {
    Literal(Literal),
    ArrayLiteral(Vec<NodeId>),
    BuiltinFunction(BuiltinFunction),

    PolymorphicArgument(usize),
    ConstAtTyping {
        inner: NodeId,
    },
    ConstAtEvaluation {
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
        args: Vec<(LocalId, NodeId)>,
        returns: NodeId,
        body: NodeId,
    },

    /// Any node within this node, is what I call a "type" node. These nodes, when typechecked, actually have their
    /// type set as their value instead of their type; their type is just "Type". The reason for that is that they're
    /// essentially a form of compile time execution, but so common that they use this system instead of the bytecode
    /// system, in the typechecker. It's similar to constant folding, but for types. And it's hacky :=)
    TypeAsValue(NodeId),
    ImplicitType,
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
    ReferenceType(NodeId, Option<PtrPermits>),
    LiteralType(Type),

    Reference(NodeId),
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
        // @Cleanup: I think right now the emitter will still emit the dummy nodes, it probably shouldn't...
        dummy_local_node: NodeId,
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
