use crate::ir::{Registers, Value};
use std::alloc::{alloc, dealloc, Layout};
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

    pub fn stack_frame<'a>(&'a mut self, registers: &'a Registers) -> StackFrame<'a> {
        if self.len < registers.buffer_size {
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

pub struct StackFrame<'a> {
    stack: &'a mut [u8],
    registers: &'a Registers,
}

impl<'a> StackFrame<'a> {
    pub fn get(&self, value: Value) -> &[u8] {
        let reg = self.registers.get(value);
        let offset = reg.offset();
        &self.stack[offset..offset + reg.size()]
    }

    pub fn get_mut(&mut self, value: Value) -> &mut [u8] {
        let reg = self.registers.get(value);
        let offset = reg.offset();
        &mut self.stack[offset..offset + reg.size()]
    }

    /// Creates a new stack frame on top of the previous one, and returns a tuple with the previous
    /// stack frame, as well as the new stack frame. This is so that the previous stack frame can
    /// still be used(although it's much smaller) while the new stackframe can add more stack
    /// frames still.
    pub fn split<'b>(&'b mut self, registers: &'b Registers) -> (StackFrame<'b>, StackFrame<'b>) {
        let position = crate::types::to_align(self.registers.buffer_size, 16);
        if self.stack.len() < position + registers.buffer_size {
            panic!("Stack overflow! (todo; show where in the code the compile time stack overflow happened)");
        }
        let (a, b) = self.stack.split_at_mut(position);
        (
            StackFrame {
                stack: a,
                registers: self.registers,
            },
            StackFrame {
                stack: b,
                registers,
            },
        )
    }
}
