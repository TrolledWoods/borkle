pub trait TreeGrowable: Default {
    type Element;

    fn append(&mut self, element: Self::Element);
}

impl TreeGrowable for () {
    type Element = ();

    fn append(&mut self, _: Self::Element) {}
}

impl<T> TreeGrowable for Vec<T> {
    type Element = T;

    fn append(&mut self, element: Self::Element) {
        self.push(element);
    }
}

impl<A, B> TreeGrowable for (A, B) where A: TreeGrowable, B: TreeGrowable {
    type Element = (A::Element, B::Element);

    fn append(&mut self, element: Self::Element) {
        self.0.append(element.0);
        self.1.append(element.1);
    }
}

pub trait TreeZippable: Sized + Default {
    type Target;
    type Reborrowed<'b>: TreeZippable where Self: 'b;

    fn ensure_len(&self, len: usize);
    fn reborrow(&mut self) -> Self::Reborrowed<'_>;
    fn slice(self, start: usize, end: usize) -> Self;
    fn split_at(self, index: usize) -> (Self, Self);
    fn split_last(self) -> (Self::Target, Self);
}

impl TreeZippable for () {
    type Target = ();
    type Reborrowed<'b> where Self: 'b = ();

    fn ensure_len(&self, _: usize) {}
    fn reborrow(&mut self) -> Self::Reborrowed<'_> { () }
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

#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Attached<A, B> {
    pub base: A,
    pub extra: B,
}

impl<A, B> std::ops::Deref for Attached<A, B> {
    type Target = A;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

impl<A, B> std::ops::DerefMut for Attached<A, B> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.base
    }
}

impl<A, B> TreeZippable for Attached<A, B> where A: TreeZippable, B: TreeZippable {
    type Target = Attached<A::Target, B::Target>;
    type Reborrowed<'b> where Self: 'b = Attached<A::Reborrowed<'b>, B::Reborrowed<'b>>;

    fn ensure_len(&self, len: usize) {
        self.base.ensure_len(len);
        self.extra.ensure_len(len);
    }
    fn reborrow(&mut self) -> Self::Reborrowed<'_> {
        Attached { base: self.base.reborrow(), extra: self.extra.reborrow() }
    }
    fn slice(self, start: usize, end: usize) -> Self {
        Attached { base: self.base.slice(start, end), extra: self.extra.slice(start, end) }
    }
    fn split_at(self, index: usize) -> (Self, Self) {
        let base = self.base.split_at(index);
        let extra = self.extra.split_at(index);
        (
            Attached { base: base.0, extra: extra.0 },
            Attached { base: base.1, extra: extra.1 },
        )
    }
    fn split_last(self) -> (Self::Target, Self) {
        let base = self.base.split_last();
        let extra = self.extra.split_last();
        (
            Attached { base: base.0, extra: extra.0 },
            Attached { base: base.1, extra: extra.1 },
        )
    }
}

impl<A, B> TreeZippable for (A, B) where A: TreeZippable, B: TreeZippable {
    type Target = (A::Target, B::Target);
    type Reborrowed<'b> where Self: 'b = (A::Reborrowed<'b>, B::Reborrowed<'b>);

    fn ensure_len(&self, len: usize) {
        self.0.ensure_len(len);
        self.1.ensure_len(len);
    }
    fn reborrow(&mut self) -> Self::Reborrowed<'_> {
        (self.0.reborrow(), self.1.reborrow())
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
    type Reborrowed<'b> where Self: 'b = &'a [T];

    fn ensure_len(&self, len: usize) { assert_eq!(self.len(), len); }
    fn reborrow(&mut self) -> Self::Reborrowed<'_> { self }
    fn slice(self, start: usize, end: usize) -> Self { &self[start..end] }
    fn split_at(self, index: usize) -> (Self, Self) { self.split_at(index) }
    fn split_last(self) -> (Self::Target, Self) { self.split_last().unwrap() }
}

impl<'a, T> TreeZippable for &'a mut [T] {
    type Target = &'a mut T;
    type Reborrowed<'b> where Self: 'b = &'b mut [T];

    fn ensure_len(&self, len: usize) { assert_eq!(self.len(), len); }
    fn reborrow(&mut self) -> Self::Reborrowed<'_> { &mut **self }
    fn slice(self, start: usize, end: usize) -> Self { &mut self[start..end] }
    fn split_at(self, index: usize) -> (Self, Self) { self.split_at_mut(index) }
    fn split_last(self) -> (Self::Target, Self) { self.split_last_mut().unwrap() }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct NodeId(pub u32);

impl From<NodeId> for usize {
    fn from(other: NodeId) -> usize {
        other.0 as usize
    }
}

#[derive(Clone, Debug)]
pub struct AstStructure {
    structure: Vec<StructuralInfo>,
}

impl AstStructure {
    pub fn len(&self) -> usize {
        self.structure.len()
    }

    pub fn root_id(&self) -> NodeId {
        NodeId(self.structure.len() as u32 - 1)
    }

    pub fn root<Z: TreeZippable>(&self, data: Z) -> GenericNodeView<'_, Z> {
        let (root, subtree) = self.structure.split_last().unwrap();
        let (zipped_root, zipped_subtree) = data.split_last();
        GenericNodeView::new(NodeId(0), root, zipped_root, subtree, zipped_subtree)
    }

    pub fn get<Z: TreeZippable>(&self, id: NodeId, data: Z) -> GenericNodeView<'_, Z> {
        let node = &self.structure[id.0 as usize];
        let base_id = id.0 - node.subtree_size;
        let nodes = &self.structure[base_id as usize..=id.0 as usize];
        let zipped = data.slice(base_id as usize, id.0 as usize + 1);
        let (head, subtree) = nodes.split_last().unwrap();
        let (zipped_head, zipped_subtree) = zipped.split_last();
        GenericNodeView::new(NodeId(base_id), head, zipped_head, subtree, zipped_subtree)
    }
}

#[derive(Clone, Debug, Default)]
pub struct AstBuilder<D: TreeGrowable> {
    nodes: Vec<StructuralInfo>,
    data: D,
}

impl<D: TreeGrowable> AstBuilder<D> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn finish(self) -> (AstStructure, D) {
        (AstStructure { structure: self.nodes }, self.data)
    }

    pub fn add(&mut self) -> AstSlot<'_, D> {
        AstSlot {
            nodes: &mut self.nodes,
            data: &mut self.data,
            num_children: 0,
        }
    }
}

/// A muncher is a more loose way of constructing an ast node, which let's you build up a list of nodes,
/// and then "munch" a few away. For example, say you have the nodes [1, 2], and you "munch" 2 and put them into plus,
/// you'll get the tree [+ [1, 2]]. Then if you added another number, [+ [1, 2], 3], and munched again into `*`, you'd
/// get [* [+ [1, 2], 3]]. So this is useful for expressions, where we don't know how deep they may get before hand.
pub struct Muncher<'a, D: TreeGrowable> {
    nodes: &'a mut Vec<StructuralInfo>,
    data: &'a mut D,
    num_nodes: u32,
}

impl<D: TreeGrowable> Muncher<'_, D> {
    pub fn add(&mut self) -> AstSlot<'_, D> {
        self.num_nodes += 1;
        AstSlot {
            nodes: self.nodes,
            data: self.data,
            num_children: 0,
        }
    }

    pub fn munch(&mut self, amount: u32, data: D::Element) -> FinishedNode {
        self.num_nodes = self.num_nodes - amount + 1;

        let slot = AstSlot {
            nodes: self.nodes,
            data: self.data,
            num_children: amount,
        };
       
        slot.finish(data)
    }

    pub fn finish(self) -> FinishedNode {
        debug_assert_eq!(self.num_nodes, 1, "A muncher has to resolve to one node in the end.");

        FinishedNode(())
    }
}

/// Pointless struct, except that it makes it basically impossible to forget to finish a node, which is great.
/// (because you can't construct the type outside of this module)
pub struct FinishedNode(());

pub struct AstSlot<'a, D: TreeGrowable> {
    nodes: &'a mut Vec<StructuralInfo>,
    data: &'a mut D,
    num_children: u32,
}

impl<'a, D: TreeGrowable> AstSlot<'a, D> {
    pub fn num_children(&self) -> u32 {
        self.num_children
    }

    pub fn add(&mut self) -> AstSlot<'_, D> {
        self.num_children += 1;
        AstSlot {
            nodes: self.nodes,
            data: self.data,
            num_children: 0,
        }
    }

    pub fn into_muncher(self) -> Muncher<'a, D> {
        debug_assert_eq!(self.num_children, 0, "You cannot convert something into a muncher when it has children already, convert before adding children");
        Muncher {
            nodes: self.nodes,
            data: self.data,
            num_nodes: 0,
        }
    }

    pub fn finish(self, data: D::Element) -> FinishedNode {
        let id_usize = self.nodes.len();

        let mut subtree_size = 0;
        let mut next_child_subtree_size = 0;
        // Go through the children in reverse(it's the only thing we can do at this point),
        // and count the total subtree size, as well as compute the next children nodes.
        for _ in 0..self.num_children {
            let child = &mut self.nodes[id_usize - subtree_size as usize - 1];
            child.next_subtree_size = next_child_subtree_size;
            next_child_subtree_size = child.subtree_size;
            subtree_size += child.subtree_size + 1;
        }

        if self.num_children >= 1 {
            // `next_child_subtree_size` will be the first child(because of backwards iteration),
            // and the last child should contain the first childs information.
            self.nodes.last_mut().unwrap().next_subtree_size = next_child_subtree_size;
        }

        self.data.append(data);
        self.nodes.push(StructuralInfo {
            subtree_size,
            next_subtree_size: 0,
            num_children: self.num_children,
        });

        FinishedNode(())
    }
}

#[derive(Clone)]
pub struct GenericChildIterator<'a, Zipped: TreeZippable> {
    munching: &'a [StructuralInfo],
    zipped: Zipped,
    base_id: NodeId,
    next_subtree_size: u32,
    num_children: u32,
}

impl<Zipped: TreeZippable> ExactSizeIterator for GenericChildIterator<'_, Zipped> {}

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
    nodes: &'a [StructuralInfo],
    zipped: Zipped,
}

impl<Zipped: TreeZippable> GenericAstSlice<'_, Zipped> {
    pub fn len(&self) -> usize {
        self.num_children as usize
    }
}

impl<'a, Zipped: TreeZippable> GenericAstSlice<'a, Zipped> {
    pub fn subtree_region(&self) -> (NodeId, usize) {
        (self.base_id, self.nodes.len())
    }

    pub fn into_array<const N: usize>(self) -> [GenericNodeView<'a, Zipped>; N] {
        use std::mem::MaybeUninit;

        assert_eq!(self.num_children as usize, N);

        let mut array: [MaybeUninit<GenericNodeView<'a, Zipped>>; N] = unsafe { MaybeUninit::uninit().assume_init() };

        array.iter_mut().zip(self).for_each(|(to, from)| { to.write(from); });

        array.map(|v| unsafe { v.assume_init() })
    }

    pub fn borrow<'b>(&'b mut self) -> GenericAstSlice<'a, Zipped::Reborrowed<'b>> {
        GenericAstSlice {
            base_id: self.base_id,
            next_subtree_size: self.next_subtree_size,
            num_children: self.num_children,
            nodes: self.nodes,
            zipped: self.zipped.reborrow(),
        }
    }

    pub fn as_array<'b, const N: usize>(&'b mut self) -> [GenericNodeView<'a, Zipped::Reborrowed<'b>>; N] {
        self.borrow().into_array()
    }
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

#[derive(Clone, Copy)]
pub struct GenericNodeView<'a, Zipped: TreeZippable> {
    pub id: NodeId,
    pub node: Zipped::Target,
    pub children: GenericAstSlice<'a, Zipped>,
}

impl<'a, Zipped: TreeZippable> GenericNodeView<'a, Zipped> {
    fn new(base_id: NodeId, node: &'a StructuralInfo, zipped_node: Zipped::Target, subtree: &'a [StructuralInfo], zipped: Zipped) -> Self {
        let next_subtree_size = subtree.last().map_or(0, |v| v.next_subtree_size);
        let num_children = node.num_children;
        Self {
            id: NodeId(base_id.0 + subtree.len() as u32),
            node: zipped_node,
            children: GenericAstSlice {
                nodes: subtree,
                base_id,
                next_subtree_size,
                num_children,
                zipped,
            },
        }
    }

    pub fn iter_all_ids(&self) -> impl Iterator<Item = NodeId> {
        let base_id = self.children.base_id.0;
        let num_children = self.children.nodes.len() as u32 + 1;

        (base_id..base_id + num_children).map(|v| NodeId(v))
    }

    pub fn subtree_region(&self) -> (NodeId, usize) {
        let (base_id, nodes) = self.children.subtree_region();
        (base_id, nodes + 1)
    }
}

impl<'a, Zipped: TreeZippable + Copy> GenericNodeView<'a, Zipped> where Zipped::Target: std::fmt::Debug + Copy {
    // Because this is a debugging function, it may be unused
    #[allow(unused)]
    pub fn print(&self) {
        let mut stack = Vec::new();
        println!("Ast:");
        println!("{}{}: {:?}", ": ".repeat(stack.len()), self.id.0, self.node);
        stack.push((self.node, self.children.into_iter()));
        while let Some((value, children)) = stack.last_mut() {
            if let Some(value) = children.next() {
                println!("{}{}: {:?}", ": ".repeat(stack.len()), value.id.0, value.node);
                stack.push((value.node, value.children.into_iter()));
            } else {
                stack.pop();
            }
        }
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

#[derive(Debug, Clone)]
struct StructuralInfo {
    /// The number of elements in total that the subtree of children contain.
    subtree_size: u32,
    /// The number of elements in the "next" subtree, so the next child in the parent.
    /// If we're the last child, and thus don't have a "next" subtree, this count means
    /// the first instead.
    next_subtree_size: u32,
    num_children: u32,
}

