use crate::program::Type;
use std::alloc;
use std::ptr::NonNull;

pub struct Constant {
    ptr: NonNull<u8>,
    type_: Type,
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
            type_,
        }
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.ptr.as_ptr()
    }
}
