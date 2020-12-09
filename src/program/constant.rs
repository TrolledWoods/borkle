use crate::types::Type;
use std::fmt;
use std::ptr::NonNull;

pub struct Constant {
    pub ptr: NonNull<u8>,
    pub size: usize,
    pub type_: Type,
}

// FIXME: Implement drop for Constant since that is like the whole point of having it in the first
// place bro

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
        unsafe { std::slice::from_raw_parts(self.as_ptr(), self.size) }
    }
}

#[derive(Clone, Copy)]
pub struct ConstantRef {
    ptr: NonNull<u8>,
}

// This is safe, because 'ConstantRef' points to immutable data
unsafe impl Sync for ConstantRef {}
unsafe impl Send for ConstantRef {}

impl ConstantRef {
    pub fn dangling() -> Self {
        Self {
            ptr: NonNull::dangling(),
        }
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.ptr.as_ptr()
    }
}

impl fmt::Debug for ConstantRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ConstantRef")
    }
}
