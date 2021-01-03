use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, Index, IndexMut};

/// A trait for ids! The required traits do not have a deep meaning other than to
/// remind you that ids should have these properties, and to not forget to derive them.
pub trait Id: Copy + Hash + Eq + From<usize> + Into<usize> {}

pub struct IdVec<I, T> {
    inner: Vec<T>,
    _phantom: PhantomData<I>,
}

impl<I, T> Default for IdVec<I, T>
where
    I: Id,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<I, T> IdVec<I, T>
where
    I: Id,
{
    pub fn new() -> Self {
        Self {
            inner: Vec::new(),
            _phantom: PhantomData,
        }
    }

    pub fn push(&mut self, element: T) -> I {
        let len = self.inner.len();
        self.inner.push(element);
        I::from(len)
    }
}

impl<I, T> Deref for IdVec<I, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<I, T> DerefMut for IdVec<I, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<I, T> Index<I> for IdVec<I, T>
where
    I: Id,
{
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        &self.inner[index.into()]
    }
}

impl<I, T> IndexMut<I> for IdVec<I, T>
where
    I: Id,
{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.inner[index.into()]
    }
}
