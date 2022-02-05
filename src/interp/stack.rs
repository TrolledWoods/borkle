use crate::ir::{StackAllocator, StackValue};
use std::alloc::{alloc, dealloc, Layout};
use std::marker::PhantomData;
use std::ptr::NonNull;

pub struct Stack {
    data: NonNull<u8>,
    len: usize,
}

impl Stack {
    pub fn new(len: usize) -> Self {
        let layout = Layout::from_size_align(len, 16).unwrap();
        let data = unsafe { NonNull::new(alloc(layout)).expect("allocation failed") };

        Self { data, len }
    }

    pub fn stack_frame<'a>(&'a mut self, registers: &'a StackAllocator) -> StackFrame<'a> {
        if self.len < registers.max {
            panic!("Stack overflow! (todo; show where in the code the compile time stack overflow happened)");
        }
        StackFrame {
            stack: unsafe { std::slice::from_raw_parts_mut(self.data.as_ptr(), self.len) },
            registers,
        }
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        let layout = Layout::from_size_align(self.len, 16).unwrap();
        unsafe {
            dealloc(self.data.as_ptr(), layout);
        }
    }
}

#[derive(Clone, Copy)]
pub struct StackValueRef<'a> {
    ptr: *const u8,
    _phantom: PhantomData<&'a u8>,
}

impl StackValueRef<'_> {
    pub fn as_ptr(self) -> *const u8 {
        self.ptr
    }

    pub unsafe fn read<T: Copy>(self) -> T {
        *self.ptr.cast()
    }
}

pub struct StackValueMut<'a> {
    ptr: *mut u8,
    _phantom: PhantomData<&'a mut u8>,
}

impl StackValueMut<'_> {
    pub fn as_ptr(&self) -> *const u8 {
        self.ptr
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.ptr
    }

    pub unsafe fn read<T: Copy>(&self) -> T {
        *self.ptr.cast()
    }

    pub unsafe fn write<T>(&self, val: T) {
        self.ptr.cast::<T>().write(val);
    }
}

pub struct StackFrame<'a> {
    stack: &'a mut [u8],
    registers: &'a StackAllocator,
}

impl<'a> StackFrame<'a> {
    pub fn len(&self) -> usize {
        self.stack.len()
    }

    pub fn into_value(self, value: StackValue) -> StackValueMut<'a> {
        let offset = value.0;
        debug_assert!(offset < self.stack.len());
        StackValueMut {
            ptr: unsafe { self.stack.as_mut_ptr().add(offset) },
            _phantom: PhantomData,
        }
    }

    pub fn get(&self, value: StackValue) -> StackValueRef<'_> {
        let offset = value.0;
        debug_assert!(offset < self.stack.len());
        StackValueRef {
            ptr: unsafe { self.stack.as_ptr().add(offset) },
            _phantom: PhantomData,
        }
    }

    pub fn get_mut(&mut self, value: StackValue) -> StackValueMut<'_> {
        let offset = value.0;
        debug_assert!(offset < self.stack.len());
        StackValueMut {
            ptr: unsafe { self.stack.as_mut_ptr().add(offset) },
            _phantom: PhantomData,
        }
    }

    /// Creates a new stack frame on top of the previous one, and returns a tuple with the previous
    /// stack frame, as well as the new stack frame. This is so that the previous stack frame can
    /// still be used(although it's much smaller) while the new stackframe can add more stack
    /// frames still.
    #[allow(unused)]
    pub fn split<'b>(&'b mut self, registers: &'b StackAllocator) -> Option<(StackFrame<'b>, StackFrame<'b>)> {
        let position = crate::types::to_align(self.registers.max, 16);
        if self.stack.len() < position + registers.max {
            return None;
        }
        let (a, b) = self.stack.split_at_mut(position);
        Some((
            StackFrame {
                stack: a,
                registers: self.registers,
            },
            StackFrame {
                stack: b,
                registers,
            },
        ))
    }
}
