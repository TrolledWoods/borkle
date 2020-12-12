use bumpalo::Bump;
use std::fmt;
use std::mem::ManuallyDrop;
use std::ops::{Deref, DerefMut};

pub struct SelfBuffer {
    buffer: Bump,
}

// We 'disable' the interior mutability of the buffer by making sure you can only push
// things with a mutable reference, so these are safe.
unsafe impl Send for SelfBuffer {}
unsafe impl Sync for SelfBuffer {}

impl SelfBuffer {
    #[must_use]
    pub fn new() -> Self {
        Self {
            buffer: Bump::new(),
        }
    }

    /// # Safety
    /// This is only safe if all the SelfBoxes inside of T are also references
    /// into this buffer. You also are not allowed to use SelfBox
    pub fn insert<T>(&mut self, data: T) -> SelfBox<T> {
        let data = self.buffer.alloc(data);

        SelfBox { data }
    }

    /// # Safety
    /// This is only safe if all the SelfBoxes inside of T are also references
    /// into this buffer. You also are not allowed to use SelfBox
    pub fn insert_root<T>(mut self, data: T) -> SelfTree<T> {
        let root = self.insert(data);

        SelfTree {
            buffer: ManuallyDrop::new(self),
            root: ManuallyDrop::new(root),
        }
    }
}

pub struct SelfTree<T> {
    buffer: ManuallyDrop<SelfBuffer>,
    root: ManuallyDrop<SelfBox<T>>,
}

impl<T> Deref for SelfTree<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &*self.root
    }
}

impl<T> DerefMut for SelfTree<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.root
    }
}

pub struct SelfBox<T> {
    data: *mut T,
}

impl<T> fmt::Debug for SelfBox<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        (&**self).fmt(fmt)
    }
}

unsafe impl<T> Send for SelfBox<T> {}
unsafe impl<T> Sync for SelfBox<T> {}

impl<T> Deref for SelfBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.data }
    }
}

impl<T> DerefMut for SelfBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data }
    }
}
