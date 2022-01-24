use crate::types::Type;
use std::alloc;
use std::fmt;
use std::ptr::NonNull;

pub struct Constant {
    pub ptr: NonNull<u8>,
    pub type_: Type,
}

impl Drop for Constant {
    fn drop(&mut self) {
        let layout = alloc::Layout::from_size_align(self.type_.size(), self.type_.align()).unwrap();
        unsafe { alloc::dealloc(self.ptr.as_ptr(), layout) };
    }
}

// Safety: Since there is no interior mutability or weirdness, in fact, no mutability in this type,
// there is no reason why it's not thread safe.
unsafe impl Sync for Constant {}
unsafe impl Send for Constant {}

impl Constant {
    pub fn as_ref(&self) -> ConstantRef {
        ConstantRef { ptr: self.ptr }
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.ptr.as_ptr()
    }

    pub fn as_slice(&self) -> &'_ [u8] {
        unsafe { std::slice::from_raw_parts(self.as_ptr(), self.type_.size()) }
    }
}

/// This is a reference to constant data in the program.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConstantRef {
    ptr: NonNull<u8>,
}

// This is "safe"(in borkle you could edit them anyway(!!!)), because 'ConstantRef' points to immutable data
unsafe impl Sync for ConstantRef {}
unsafe impl Send for ConstantRef {}

impl ConstantRef {
    pub fn dangling() -> Self {
        Self {
            ptr: NonNull::dangling(),
        }
    }

    pub fn as_ptr(self) -> *const u8 {
        self.ptr.as_ptr()
    }
}

impl fmt::Debug for ConstantRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ConstantRef {}", self.as_ptr() as usize)
    }
}
