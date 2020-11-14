use bumpalo::Bump;
use impl_twice::impl_twice;
use std::marker::PhantomData;
use std::mem::transmute;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

pub struct Tree<T: 'static> {
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

impl<T> Tree<T> {
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

pub struct NodeBuilder<'a, T: 'static> {
    // Invariant: All the nodese in incomplete are supposed
    // to be allocated within the tree.
    tree: &'a mut Tree<T>,
    starting_point: usize,
    value: Option<T>,
}

impl<T> NodeBuilder<'_, T> {
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

    pub fn arg_with(&mut self, value: T) -> NodeBuilder<'_, T> {
        let mut arg = self.arg();
        arg.set(value);
        arg
    }
}

impl<T> Drop for NodeBuilder<'_, T> {
    fn drop(&mut self) {
        let slice = self
            .tree
            .bump
            .alloc_slice_fill_iter(self.tree.incomplete.drain(self.starting_point..));

        self.tree.incomplete.push(InternalNode {
            children: to_non_null(slice),
            value: self
                .value
                .take()
                .expect("You have to set the value of a NodeBuilder before dropping it."),
        });

        assert_eq!(self.tree.incomplete.len(), self.starting_point + 1);
    }
}

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
    Deref for Node<'_, T>,
    Deref for NodeMut<'_, T>
{
    type Target = T;

    fn deref(&self) -> &'_ Self::Target {
        &self.internal.value
    }
}
);

impl<T> DerefMut for NodeMut<'_, T> {
    fn deref_mut(&mut self) -> &'_ mut Self::Target {
        &mut self.internal.value
    }
}

struct InternalNode<T> {
    // Invariant: These children have to have been
    // allocated within the same tree. This is because
    // Nodes are deallocated together
    children: NonNull<[InternalNode<T>]>,
    value: T,
}

fn to_non_null<T: ?Sized>(value: &mut T) -> NonNull<T> {
    // Safety: &mut is never null.
    unsafe { NonNull::new_unchecked(value) }
}
