use crate::program::Type;
use std::alloc;
use std::borrow::Borrow;
use std::cmp::{Eq, PartialEq};
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::ptr::NonNull;

pub struct Constant {
    ptr: NonNull<u8>,
    size: usize,
}

// Safety: Since there is no interior mutability or weirdness, in fact, no mutability in this type,
// there is no reason why it's not thread safe.
unsafe impl Sync for Constant {}
unsafe impl Send for Constant {}

impl Constant {
    /// Creates a new heap allocated `Constant` by copying
    /// the type from the given ptr.
    pub unsafe fn create(type_: Type, from: *const u8) -> Self {
        let ptr = alloc::alloc(type_.layout());

        std::ptr::copy(from, ptr, type_.size());

        Self {
            ptr: NonNull::new(ptr).unwrap(),
            size: type_.size(),
        }
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.ptr.as_ptr()
    }

    pub fn as_non_null(&self) -> NonNull<u8> {
        self.ptr
    }

    pub fn as_slice(&self) -> &'_ [u8] {
        unsafe { std::slice::from_raw_parts(self.as_ptr(), self.size) }
    }
}

impl PartialEq for Constant {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Eq for Constant {}

impl Hash for Constant {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.as_slice().hash(hasher);
    }
}

impl Deref for Constant {
    type Target = [u8];

    fn deref(&self) -> &'_ Self::Target {
        self.as_slice()
    }
}

impl Borrow<[u8]> for Constant {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}
