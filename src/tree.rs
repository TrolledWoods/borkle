use bumpalo::Bump;
use impl_twice::impl_twice;
use std::fmt::{self, Debug};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

pub trait MetaData: Sized {
    fn validate(&self, num_args: usize) -> bool;
}

pub struct Tree<T> {
    // Invariants:
    // * All the pointers in the tree point to inside the
    // bump allocator. Since the bump allocator uses heap allocations,
    // moving the Ast won't invalidate the pointers.
    // * The pointers are all 'static Box:es, Box:es because I
    // wanted to make sure that they are dropped, and 'static
    // because this datastructure itself makes sure that
    // the bump allocator isn't deallocated before the tree is,
    // so we want the borrow checker to shut up for a second.
    bump: Bump,
    root: Option<InternalNode<T>>,
    incomplete: Vec<InternalNode<T>>,
}

impl<T> Tree<T>
where
    T: MetaData,
{
    pub fn new() -> Self {
        let bump = Bump::new();
        Self {
            bump,
            root: None,
            incomplete: Vec::new(),
        }
    }

    pub fn builder(&mut self) -> NodeBuilder<'_, T> {
        NodeBuilder {
            starting_point: self.incomplete.len(),
            tree: self,
            value: None,
        }
    }

    /// Sets the root of the tree. This requires exactly one builder to have
    /// done stuff beforehand.
    pub fn set_root(&mut self) {
        assert_eq!(self.incomplete.len(), 1);
        self.root = Some(self.incomplete.pop().unwrap());
    }

    pub fn root(&self) -> Option<Node<'_, T>> {
        self.root.as_ref().map(|internal| Node { internal })
    }

    pub fn root_mut(&mut self) -> Option<NodeMut<'_, T>> {
        self.root.as_mut().map(|internal| NodeMut { internal })
    }
}

impl<T> Debug for Tree<T>
where
    T: Debug + MetaData,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.root() {
            Some(root) => root.fmt(fmt),
            None => write!(fmt, "No root"),
        }
    }
}

impl<T> Drop for Tree<T> {
    fn drop(&mut self) {
        // We have to make sure to drop these before we drop the bump allocator.
        // If the bump allocator is dropped before these, these will access
        // dangling memory.
        let _ = self.root.take();
        self.incomplete.clear();
    }
}

pub struct NodeBuilder<'a, T: MetaData> {
    // Invariant: All the nodese in incomplete are supposed
    // to be allocated within the tree.
    tree: &'a mut Tree<T>,
    starting_point: usize,
    value: Option<T>,
}

impl<T> NodeBuilder<'_, T>
where
    T: MetaData,
{
    pub fn set(&mut self, value: T) {
        assert!(
            self.value.is_none(),
            "Cannot set when there is already a value"
        );
        self.value = Some(value);
    }

    pub fn arg(&mut self) -> NodeBuilder<'_, T> {
        self.tree.builder()
    }

    /// Replaces this node with a single argument of this node.
    /// This is useful if you need to specify something as an
    /// argument but then only later know if it is actually supposed
    /// to be an argument or its own node entirely.
    ///
    /// # Panics
    /// * If the `set` method has been called before
    /// * If there isn't exactly one argument
    pub fn into_arg(self) {
        assert!(self.value.is_none());
        assert_eq!(self.tree.incomplete.len(), self.starting_point + 1);

        // Don't call drop to make this its own node.
        std::mem::forget(self);
    }

    /// Panics if the node builder isn't in a valid state.
    ///
    /// Also panics if nothing is set.
    pub fn validate(self) {
        let num_arguments = self.tree.incomplete.len() - self.starting_point;
        let value = self
            .value
            .as_ref()
            .expect("The value of a NodeBuilder has to be set before validating it.");
        assert!(value.validate(num_arguments), "Validation failed");
    }
}

impl<T> NodeBuilder<'_, T>
where
    T: Clone + MetaData,
{
    /// A way to clone nodes from a different ast into
    /// this one.
    pub fn set_cloned(&mut self, other: &Node<'_, T>) {
        self.set(other.internal.value.clone());

        for child in other.children() {
            self.arg().set_cloned(&child);
        }
    }
}

impl<T> Drop for NodeBuilder<'_, T>
where
    T: MetaData,
{
    fn drop(&mut self) {
        if let Some(value) = self.value.take() {
            let slice = self
                .tree
                .bump
                .alloc_slice_fill_iter(self.tree.incomplete.drain(self.starting_point..));

            self.tree.incomplete.push(InternalNode {
                children: to_non_null(slice),
                value,
            });

            debug_assert_eq!(self.tree.incomplete.len(), self.starting_point + 1);
        }
    }
}

#[derive(Clone, Copy)]
pub struct Node<'a, T> {
    internal: &'a InternalNode<T>,
}

pub struct NodeMut<'a, T> {
    // The reason this is wrapping an InternalNode
    // is so that we can't swap nodes out. That would be bad
    // because it breaks the invariant that nodes can only come
    // from the same tree.
    internal: &'a mut InternalNode<T>,
}

impl_twice!(
impl<T>
    Debug for Node<'_, T>,
    Debug for NodeMut<'_, T>
where (T: Debug) {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.internal.value.fmt(fmt)?;
        write!(fmt, ": ")?;
        fmt.debug_list().entries(self.children()).finish()
    }
}


impl<T>
    Deref for Node<'_, T>,
    Deref for NodeMut<'_, T>
{
    type Target = T;

    fn deref(&self) -> &'_ Self::Target {
        &self.internal.value
    }
}

impl<T> Node<'_, T>, NodeMut<'_, T> {
    fn children_slice(&self) -> &[InternalNode<T>] {
        unsafe {
            &*self.internal.children.as_ptr()
        }
    }

    #[allow(unused)]
    pub fn child_count(&self) -> usize {
        self.children_slice().len()
    }

    #[allow(unused)]
    pub fn children(&self) -> impl Iterator<Item = Node<'_, T>> + DoubleEndedIterator + ExactSizeIterator {
        self.children_slice().iter().map(|v| Node { internal: v })
    }
}
);

impl<T> NodeMut<'_, T> {
    #[allow(unused)]
    pub fn children_mut(
        &mut self,
    ) -> impl Iterator<Item = NodeMut<'_, T>> + DoubleEndedIterator + ExactSizeIterator {
        let children = unsafe { &mut *self.internal.children.as_ptr() };

        children.iter_mut().map(|v| NodeMut { internal: v })
    }
}

impl<T> DerefMut for NodeMut<'_, T> {
    fn deref_mut(&mut self) -> &'_ mut Self::Target {
        &mut self.internal.value
    }
}

struct InternalNode<T> {
    // Invariant: These children have to have been
    // allocated within the same tree. This is because
    // we play with lifetimes here, and if nodes from
    // different trees were to come in here they would
    // not work because the lifetimes are different.
    children: NonNull<[InternalNode<T>]>,
    value: T,
}

impl<T> Drop for InternalNode<T> {
    fn drop(&mut self) {
        unsafe {
            self.children.as_ptr().drop_in_place();
        }
    }
}

fn to_non_null<T: ?Sized>(value: &mut T) -> NonNull<T> {
    // Safety: &mut is never null.
    unsafe { NonNull::new_unchecked(value) }
}
