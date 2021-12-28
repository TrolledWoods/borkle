use crate::literal::Literal;
use crate::locals::{LabelId, LocalId};
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::constant::ConstantRef;
use crate::program::{BuiltinFunction, MemberId, MemberMetaData, ScopeId};
use crate::types::Type;
use std::fmt;
use std::sync::Arc;
use ustr::Ustr;

pub trait TreeZippable: Sized + Default {
    type Target;

    fn ensure_len(&self, len: usize);
    fn slice(self, start: usize, end: usize) -> Self;
    fn split_at(self, index: usize) -> (Self, Self);
    fn split_last(self) -> (Self::Target, Self);
}

impl TreeZippable for () {
    type Target = ();

    fn ensure_len(&self, _: usize) {}
    fn slice(self, _: usize, _: usize) -> Self {
        ()
    }
    fn split_at(self, _: usize) -> (Self, Self) {
        ((), ())
    }
    fn split_last(self) -> (Self::Target, Self) {
        ((), ())
    }
}

impl<A, B> TreeZippable for (A, B) where A: TreeZippable, B: TreeZippable {
    type Target = (A::Target, B::Target);

    fn ensure_len(&self, len: usize) {
        self.0.ensure_len(len);
        self.1.ensure_len(len);
    }
    fn slice(self, start: usize, end: usize) -> Self {
        (self.0.slice(start, end), self.1.slice(start, end))
    }
    fn split_at(self, index: usize) -> (Self, Self) {
        let a = self.0.split_at(index);
        let b = self.1.split_at(index);
        ((a.0, b.0), (a.1, b.1))
    }
    fn split_last(self) -> (Self::Target, Self) {
        let a = self.0.split_last();
        let b = self.1.split_last();
        ((a.0, b.0), (a.1, b.1))
    }
}

impl<'a, T> TreeZippable for &'a [T] {
    type Target = &'a T;

    fn ensure_len(&self, len: usize) { assert_eq!(self.len(), len); }
    fn slice(self, start: usize, end: usize) -> Self { &self[start..end] }
    fn split_at(self, index: usize) -> (Self, Self) { self.split_at(index) }
    fn split_last(self) -> (Self::Target, Self) { self.split_last().unwrap() }
}

impl<'a, T> TreeZippable for &'a mut [T] {
    type Target = &'a mut T;

    fn ensure_len(&self, len: usize) { assert_eq!(self.len(), len); }
    fn slice(self, start: usize, end: usize) -> Self { &mut self[start..end] }
    fn split_at(self, index: usize) -> (Self, Self) { self.split_at_mut(index) }
    fn split_last(self) -> (Self::Target, Self) { self.split_last_mut().unwrap() }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct NodeId(pub u32);

#[derive(Clone, Debug)]
pub struct Ast {
    builder: AstBuilder,
}

impl Ast {
    // Because this is a debugging function, it may be unused
    #[allow(unused)]
    pub fn print(&self) {
        let mut stack = Vec::new();
        println!("Ast:");
        println!("{}{}: {:?}", ": ".repeat(stack.len()), self.root().id.0, self.root().node.kind);
        stack.push((self.root().node, self.root().children.into_iter()));
        while let Some((value, children)) = stack.last_mut() {
            if let Some(value) = children.next() {
                println!("{}{}: {:?}", ": ".repeat(stack.len()), value.id.0, value.node.kind);
                stack.push((value.node, value.children.into_iter()));
            } else {
                stack.pop();
            }
        }
    }
    
    pub fn root_id(&self) -> NodeId {
        NodeId(self.builder.nodes.len() as u32 - 1)
    }

    pub fn root(&self) -> NodeView<'_> {
        let (root, subtree) = self.builder.nodes.split_last().unwrap();
        NodeView::new(NodeId(0), root, subtree)
    }

    pub fn root_mut(&mut self) -> NodeViewMut<'_> {
        let (root, subtree) = self.builder.nodes.split_last_mut().unwrap();
        NodeViewMut::new(NodeId(0), root, subtree)
    }

    pub fn get(&self, id: NodeId) -> NodeView<'_> {
        let node = &self.builder.nodes[id.0 as usize];
        let base_id = id.0 - node.subtree_size;
        let nodes = &self.builder.nodes[base_id as usize..=id.0 as usize];
        let (head, subtree) = nodes.split_last().unwrap();
        NodeView::new(NodeId(base_id), head, subtree)
    }

    pub fn get_mut(&mut self, id: NodeId) -> NodeViewMut<'_> {
        let node = &mut self.builder.nodes[id.0 as usize];
        let base_id = id.0 - node.subtree_size;
        let nodes = &mut self.builder.nodes[base_id as usize..=id.0 as usize];
        let (head, subtree) = nodes.split_last_mut().unwrap();
        NodeViewMut::new(NodeId(base_id), head, subtree)
    }
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

    pub fn finish(self) -> Ast {
        // @Performance: This is not necessary, it's just to make sure that everything
        // is correct
        for node in self.nodes.iter().rev().skip(1).rev() {
            if node.parent.is_none() {
                panic!("Node without a parent {:?}", node);
            }
        }

        Ast {
            builder: self,
        }
    }

    pub fn add(&mut self) -> AstSlot<'_> {
        AstSlot {
            nodes: &mut self.nodes,
            num_children: 0,
        }
    }
}

/// A muncher is a more loose way of constructing an ast node, which let's you build up a list of nodes,
/// and then "munch" a few away. For example, say you have the nodes [1, 2], and you "munch" 2 and put them into plus,
/// you'll get the tree [+ [1, 2]]. Then if you added another number, [+ [1, 2], 3], and munched again into `*`, you'd
/// get [* [+ [1, 2], 3]]. So this is useful for expressions, where we don't know how deep they may get before hand.
pub struct Muncher<'a> {
    nodes: &'a mut Vec<Node>,
    num_nodes: u32,
}

impl Muncher<'_> {
    pub fn add(&mut self) -> AstSlot<'_> {
        self.num_nodes += 1;
        AstSlot {
            nodes: &mut *self.nodes,
            num_children: 0,
        }
    }

    pub fn munch(&mut self, amount: u32, loc: Location, kind: NodeKind) -> FinishedNode {
        self.num_nodes = self.num_nodes - amount + 1;

        let slot = AstSlot {
            nodes: self.nodes,
            num_children: amount,
        };
       
        slot.finish(loc, kind)
    }

    pub fn finish(self) -> FinishedNode {
        debug_assert_eq!(self.num_nodes, 1, "A muncher has to resolve to one node in the end.");

        FinishedNode(())
    }
}

/// Pointless struct, except that it makes it basically impossible to forget to finish a node, which is great.
/// (because you can't construct the type outside of this module)
pub struct FinishedNode(());

pub struct AstSlot<'a> {
    nodes: &'a mut Vec<Node>,
    num_children: u32,
}

impl<'a> AstSlot<'a> {
    pub fn add(&mut self) -> AstSlot<'_> {
        self.num_children += 1;
        AstSlot {
            nodes: &mut *self.nodes,
            num_children: 0,
        }
    }

    pub fn into_muncher(self) -> Muncher<'a> {
        debug_assert_eq!(self.num_children, 0, "You cannot convert something into a muncher when it has children already, convert before adding children");
        Muncher {
            nodes: self.nodes,
            num_nodes: 0,
        }
    }

    pub fn finish(self, loc: Location, kind: NodeKind) -> FinishedNode {
        let id_usize = self.nodes.len();
        let id = NodeId(u32::try_from(id_usize).expect("Ast overflow!"));

        let mut subtree_size = 0;
        let mut next_child_subtree_size = 0;
        // Go through the children in reverse(it's the only thing we can do at this point),
        // and count the total subtree size, as well as compute the next children nodes.
        for _ in 0..self.num_children {
            let child = &mut self.nodes[id_usize - subtree_size as usize - 1];
            child.parent = Some(id);
            child.next_subtree_size = next_child_subtree_size;
            next_child_subtree_size = child.subtree_size;
            subtree_size += child.subtree_size + 1;
        }

        if self.num_children >= 1 {
            // `next_child_subtree_size` will be the first child(because of backwards iteration),
            // and the last child should contain the first childs information.
            self.nodes.last_mut().unwrap().next_subtree_size = next_child_subtree_size;
        }

        self.nodes.push(Node {
            loc,
            kind,
            parent: None,
            type_infer_value_id: crate::type_infer::ValueId::NONE,
            type_: None,
            subtree_size,
            next_subtree_size: 0,
            num_children: self.num_children,
        });

        FinishedNode(())
    }
}

#[derive(Clone)]
pub struct ChildIterator<'a> {
    munching: &'a [Node],
    base_id: NodeId,
    next_subtree_size: u32,
    num_children: u32,
}

impl<'a> Iterator for ChildIterator<'a> {
    type Item = NodeView<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.num_children == 0 { return None; }
        self.num_children -= 1;

        let munching = std::mem::replace(&mut self.munching, &[]);
        let (child_section, new_munching) = munching.split_at(self.next_subtree_size as usize + 1);
        let old_base = self.base_id;
        self.base_id = NodeId(self.base_id.0 + self.next_subtree_size + 1);
        self.munching = new_munching;

        let (child, child_subtree) = child_section.split_last().unwrap();
        self.next_subtree_size = child.next_subtree_size;

        Some(NodeView::new(old_base, child, child_subtree))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_children as usize, Some(self.num_children as usize))
    }
}

impl ExactSizeIterator for ChildIterator<'_> {}

pub struct ChildIteratorMut<'a> {
    munching: &'a mut [Node],
    base_id: NodeId,
    next_subtree_size: u32,
    num_children: u32,
}

impl<'a> Iterator for ChildIteratorMut<'a> {
    type Item = NodeViewMut<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.num_children == 0 { return None; }
        self.num_children -= 1;

        let munching = std::mem::replace(&mut self.munching, &mut []);
        let (child_section, new_munching) = munching.split_at_mut(self.next_subtree_size as usize + 1);
        let old_base = self.base_id;
        self.base_id = NodeId(self.base_id.0 + self.next_subtree_size + 1);
        self.munching = new_munching;

        let (child, child_subtree) = child_section.split_last_mut().unwrap();
        self.next_subtree_size = child.next_subtree_size;

        Some(NodeViewMut::new(old_base, child, child_subtree))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_children as usize, Some(self.num_children as usize))
    }
}

impl ExactSizeIterator for ChildIteratorMut<'_> {}

#[derive(Clone, Copy)]
pub struct AstSlice<'a> {
    base_id: NodeId,
    next_subtree_size: u32,
    num_children: u32,
    nodes: &'a [Node],
}

impl<'a> IntoIterator for AstSlice<'a> {
    type IntoIter = ChildIterator<'a>;
    type Item = NodeView<'a>;

    fn into_iter(self) -> Self::IntoIter {
        ChildIterator {
            munching: self.nodes,
            base_id: self.base_id,
            next_subtree_size: self.next_subtree_size,
            num_children: self.num_children,
        }
    }
}

pub struct AstSliceMut<'a> {
    base_id: NodeId,
    next_subtree_size: u32,
    num_children: u32,
    nodes: &'a mut [Node],
}

impl<'a> AstSliceMut<'a> {
    pub fn into_array<const N: usize>(self) -> [NodeViewMut<'a>; N] {
        use std::mem::MaybeUninit;

        assert_eq!(self.num_children as usize, N);

        let mut array: [MaybeUninit<NodeViewMut<'_>>; N] = unsafe { MaybeUninit::uninit().assume_init() };

        array.iter_mut().zip(self).for_each(|(to, from)| { to.write(from); });

        array.map(|v| unsafe { v.assume_init() })
    }
}

impl<'a> IntoIterator for AstSliceMut<'a> {
    type IntoIter = ChildIteratorMut<'a>;
    type Item = NodeViewMut<'a>;

    fn into_iter(self) -> Self::IntoIter {
        ChildIteratorMut {
            munching: self.nodes,
            base_id: self.base_id,
            next_subtree_size: self.next_subtree_size,
            num_children: self.num_children,
        }
    }
}

pub struct GenericChildIterator<'a, Zipped: TreeZippable> {
    munching: &'a [Node],
    zipped: Zipped,
    base_id: NodeId,
    next_subtree_size: u32,
    num_children: u32,
}

impl<'a, Zipped: TreeZippable> Iterator for GenericChildIterator<'a, Zipped> {
    type Item = GenericNodeView<'a, Zipped>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.num_children == 0 { return None; }
        self.num_children -= 1;

        let munching = std::mem::take(&mut self.munching);
        let zipped = std::mem::take(&mut self.zipped);
        let (child_section, new_munching) = munching.split_at(self.next_subtree_size as usize + 1);
        let (child_zipped, new_zipped) = zipped.split_at(self.next_subtree_size as usize + 1);
        let old_base = self.base_id;
        self.base_id = NodeId(self.base_id.0 + self.next_subtree_size + 1);
        self.munching = new_munching;
        self.zipped = new_zipped;

        let (child, child_subtree) = child_section.split_last().unwrap();
        let (zipped_child, child_zipped_subtree) = child_zipped.split_last();
        self.next_subtree_size = child.next_subtree_size;

        Some(GenericNodeView::new(old_base, child, zipped_child, child_subtree, child_zipped_subtree))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num_children as usize, Some(self.num_children as usize))
    }
}

#[derive(Clone, Copy)]
pub struct GenericAstSlice<'a, Zipped: TreeZippable> {
    base_id: NodeId,
    next_subtree_size: u32,
    num_children: u32,
    nodes: &'a [Node],
    zipped: Zipped,
}

impl<'a, Zipped: TreeZippable> IntoIterator for GenericAstSlice<'a, Zipped> {
    type IntoIter = GenericChildIterator<'a, Zipped>;
    type Item = GenericNodeView<'a, Zipped>;

    fn into_iter(self) -> Self::IntoIter {
        GenericChildIterator {
            munching: self.nodes,
            base_id: self.base_id,
            next_subtree_size: self.next_subtree_size,
            num_children: self.num_children,
            zipped: self.zipped,
        }
    }
}

pub struct GenericNodeView<'a, Zipped: TreeZippable> {
    pub id: NodeId,
    pub node: Zipped::Target,
    internal_node: &'a Node,
    pub children: GenericAstSlice<'a, Zipped>,
}

impl<'a, Zipped: TreeZippable> GenericNodeView<'a, Zipped> {
    fn new(base_id: NodeId, node: &'a Node, zipped_node: Zipped::Target, subtree: &'a [Node], zipped: Zipped) -> Self {
        let next_subtree_size = subtree.last().map_or(0, |v| v.next_subtree_size);
        let num_children = node.num_children;
        Self {
            id: NodeId(base_id.0 + subtree.len() as u32),
            node: zipped_node,
            internal_node: node,
            children: GenericAstSlice {
                nodes: subtree,
                base_id,
                next_subtree_size,
                num_children,
                zipped,
            },
        }
    }
}

impl<'a, Zipped: TreeZippable + Copy> GenericNodeView<'a, Zipped> {
    pub fn children_array<const N: usize>(&self) -> [Self; N] {
        use std::mem::MaybeUninit;

        assert_eq!(self.internal_node.num_children as usize, N);

        let mut array: [MaybeUninit<Self>; N] = unsafe { MaybeUninit::uninit().assume_init() };

        array.iter_mut().zip(self.children).for_each(|(to, from)| { to.write(from); });

        array.map(|v| unsafe { v.assume_init() })
    }
}

impl<'a, Zipped: TreeZippable> std::ops::Deref for GenericNodeView<'a, Zipped> {
    type Target = Zipped::Target;

    fn deref(&self) -> &Self::Target {
        &self.node
    }
}

impl<'a, Zipped: TreeZippable> std::ops::DerefMut for GenericNodeView<'a, Zipped> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.node
    }
}

#[derive(Clone)]
pub struct NodeView<'a> {
    pub id: NodeId,
    pub node: &'a Node,
    pub children: AstSlice<'a>,
}

impl<'a> NodeView<'a> {
    fn new(base_id: NodeId, node: &'a Node, subtree: &'a [Node]) -> Self {
        let next_subtree_size = subtree.last().map_or(0, |v| v.next_subtree_size);
        let num_children = node.num_children;
        Self {
            id: NodeId(base_id.0 + subtree.len() as u32),
            node,
            children: AstSlice {
                nodes: subtree,
                base_id,
                next_subtree_size,
                num_children,
            },
        }
    }

    pub fn children_array<const N: usize>(&self) -> [NodeView<'a>; N] {
        use std::mem::MaybeUninit;

        assert_eq!(self.num_children as usize, N);

        let mut array: [MaybeUninit<NodeView<'a>>; N] = unsafe { MaybeUninit::uninit().assume_init() };

        array.iter_mut().zip(self.children.clone()).for_each(|(to, from)| { to.write(from); });

        array.map(|v| unsafe { v.assume_init() })
    }
}

impl std::ops::Deref for NodeView<'_> {
    type Target = Node;

    fn deref(&self) -> &Self::Target {
        self.node
    }
}

pub struct NodeViewMut<'a> {
    pub id: NodeId,
    pub node: &'a mut Node,
    pub children: AstSliceMut<'a>,
}

impl<'a> NodeViewMut<'a> {
    fn new(base_id: NodeId, node: &'a mut Node, subtree: &'a mut [Node]) -> Self {
        let next_subtree_size = subtree.last().map_or(0, |v| v.next_subtree_size);
        let num_children = node.num_children;
        Self {
            id: NodeId(base_id.0 + subtree.len() as u32),
            node,
            children: AstSliceMut {
                nodes: subtree,
                base_id,
                next_subtree_size,
                num_children,
            },
        }
    }
}

impl std::ops::Deref for NodeViewMut<'_> {
    type Target = Node;

    fn deref(&self) -> &Self::Target {
        &*self.node
    }
}

impl std::ops::DerefMut for NodeViewMut<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.node
    }
}

#[derive(Clone)]
pub struct Node {
    pub loc: Location,
    pub kind: NodeKind,
    pub parent: Option<NodeId>,
    pub type_infer_value_id: crate::type_infer::ValueId,
    pub type_: Option<Type>,

    /// The number of elements in total that the subtree of children contain.
    subtree_size: u32,
    /// The number of elements in the "next" subtree, so the next child in the parent.
    /// If we're the last child, and thus don't have a "next" subtree, this count means
    /// the first instead.
    next_subtree_size: u32,
    pub num_children: u32,
}

impl Node {
    pub fn type_(&self) -> Type {
        self.type_.unwrap()
    }
}

#[derive(Debug, Clone)]
pub enum NodeKind {
    Literal(Literal),
    ArrayLiteral,
    BuiltinFunction(BuiltinFunction),

    Explain,

    PolymorphicArgument(usize),
    ConstAtTyping,
    ConstAtEvaluation,

    Global {
        scope: ScopeId,
        name: Ustr,
    },

    /// [ of, ..args ]
    PolymorphicArgs,

    Constant(ConstantRef, Option<Arc<MemberMetaData>>),
    ResolvedGlobal(MemberId, Arc<MemberMetaData>),

    /// [ iterator, body, else_body ]
    For {
        iterator: LocalId,
        iteration_var: LocalId,
        label: LabelId,
    },
    /// [ condition, body, else_body ]
    While {
        iteration_var: LocalId,
        label: LabelId,
    },
    /// [ condition, body, else_body ]
    If {
        is_const: Option<Location>,
    },

    Member {
        name: Ustr,
    },

    /// [ .. args, returns, body ]  (at least 2 children)
    FunctionDeclaration {
        args: Vec<LocalId>,
    },

    /// [ inner ]
    TypeOf,
    /// [ inner ]
    SizeOf,
    /// Type expressions actually use the type of the node to mean the type of the expression. So if you were to do
    /// &T, this would have the type &T. This of course, isn't compatible with how normal expressions work, so we
    /// need this node to convert from the way type expressions work to the way values work, by taking the type of the
    /// type expression, inserting it into the global type table, and then making that value a constant. (and the type
    /// is of course `Type`). Except that this isn't the full story, in reality type expressions are what's called
    /// "inferrable constants", which means that if you use a `type`, inside of a type, it just "disappears", and
    /// allows for inferrence through it. This is vital for allowing constants with `type` to behave as you'd expect.
    /// [ inner ]
    TypeAsValue,
    ImplicitType,
    /// [ .. fields ]
    StructType {
        fields: Vec<Ustr>,
    },
    /// [ len, member ]
    ArrayType,
    /// [ .. args, returns ]
    FunctionType,
    /// [ inner ]
    BufferType,
    /// [ inner ]
    ReferenceType,
    LiteralType(Type),
    /// [ inner ]
    Reference,
    /// [ operand ]
    Unary {
        op: UnaryOp,
    },
    /// [ left, right ]
    Binary {
        op: BinaryOp,
    },
    /// [ expression ]
    Break {
        label: LabelId,
        num_defer_deduplications: usize,
    },
    /// [ inner ]
    Defer,
    /// [ calling, .. args ]
    FunctionCall,
    /// [ calling, .. args ]
    ResolvedFunctionCall {
        arg_indices: Vec<usize>,
    },
    /// [ .. contents ]
    Block {
        label: Option<LabelId>,
    },
    /// [ inner ]
    Parenthesis,
    Empty,
    Uninit,
    Zeroed,

    /// [ value, bound ]
    TypeBound,
    /// [ inner ]
    Cast,
    /// [ inner ]
    BitCast,
    /// [ value ]
    Declare {
        local: LocalId,
    },
    Local(LocalId),
}

impl fmt::Debug for Node {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(fmt)
    }
}
