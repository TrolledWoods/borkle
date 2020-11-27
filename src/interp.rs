use crate::ir::{Instr, Routine};
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::Program;
use crate::types::TypeKind;

#[macro_use]
mod macros;
mod stack;

pub use stack::Stack;
use stack::StackFrame;

pub fn interp(program: &Program, stack: &mut Stack, routine: &Routine) -> Vec<u8> {
    let mut stack_frame = stack.stack_frame(&routine.registers);
    interp_internal(program, &mut stack_frame, routine);
    stack_frame.get(routine.result).into()
}

// The stack frame has to be set up ahead of time here. That is necessary; because
// we need some way to access the result afterwards as well.
fn interp_internal(program: &Program, stack: &mut StackFrame<'_>, routine: &Routine) {
    for instr in &routine.instr {
        match *instr {
            Instr::CallExtern {
                to,
                pointer,
                ref args,
                convention,
            } => {
                let mut ptr = [0_u8; 8];
                ptr.copy_from_slice(stack.get(pointer));
                let function_ptr = unsafe { std::mem::transmute(usize::from_le_bytes(ptr)) };

                let mut arg_pointers = [std::ptr::null_mut(); crate::MAX_FUNCTION_ARGUMENTS];
                for (arg_ptr, &arg) in arg_pointers.iter_mut().zip(args) {
                    *arg_ptr = stack.get_mut(arg).as_mut_ptr().cast();
                }

                let to_ptr: *mut _ = stack.get_mut(to).as_mut_ptr().cast();

                unsafe {
                    convention.call(function_ptr, arg_pointers.as_mut_ptr(), to_ptr);
                }
            }
            Instr::Constant { to, ref from } => {
                stack.get_mut(to).copy_from_slice(from);
            }
            Instr::Global { to, from } => {
                program.copy_value_into_slice(from, stack.get_mut(to));
            }
            Instr::Binary {
                op,
                to,
                a,
                b,
                type_,
            } => match op {
                BinaryOp::And | BinaryOp::Or | BinaryOp::Equals => {
                    todo!("Operator is not implemented yet");
                }
                BinaryOp::Add => {
                    if let TypeKind::Int(int) = *type_.kind() {
                        all_int_types!(int, stack.get_mut(to), (stack.get(a), stack.get(b)), +);
                    } else {
                        todo!();
                    }
                }
                BinaryOp::Sub => {
                    if let TypeKind::Int(int) = *type_.kind() {
                        all_int_types!(int, stack.get_mut(to), (stack.get(a), stack.get(b)), -);
                    } else {
                        todo!();
                    }
                }
                BinaryOp::Mult => {
                    if let TypeKind::Int(int) = *type_.kind() {
                        all_int_types!(int, stack.get_mut(to), (stack.get(a), stack.get(b)), *);
                    } else {
                        todo!();
                    }
                }
                BinaryOp::Div => {
                    if let TypeKind::Int(int) = *type_.kind() {
                        all_int_types!(int, stack.get_mut(to), (stack.get(a), stack.get(b)), /);
                    } else {
                        todo!();
                    }
                }
                BinaryOp::BitAnd => {
                    if let TypeKind::Int(int) = *type_.kind() {
                        all_int_types!(int, stack.get_mut(to), (stack.get(a), stack.get(b)), &);
                    } else {
                        todo!();
                    }
                }
                BinaryOp::BitOr => {
                    if let TypeKind::Int(int) = *type_.kind() {
                        all_int_types!(int, stack.get_mut(to), (stack.get(a), stack.get(b)), |);
                    } else {
                        todo!();
                    }
                }
            },
            Instr::Unary { op, to, from } => match op {
                UnaryOp::Negate => {
                    let from = u64_from_bytes(stack.get(from));
                    let result = from.wrapping_neg();
                    let to = stack.get_mut(to);
                    to.copy_from_slice(&result.to_le_bytes()[..to.len()]);
                }
                UnaryOp::Not => {
                    let from = u64_from_bytes(stack.get(from));
                    let result = !from;
                    let to = stack.get_mut(to);
                    to.copy_from_slice(&result.to_le_bytes()[..to.len()]);
                }
                UnaryOp::Reference | UnaryOp::Dereference => {
                    unreachable!("This operator is supposed to be a special case");
                }
            },
            Instr::Member { .. } => {
                todo!();
            }
            Instr::Dereference { to, from } => {
                let mut arr = [0_u8; 8];
                arr.copy_from_slice(stack.get(from));
                let ptr = usize::from_le_bytes(arr) as *const u8;

                let to = stack.get_mut(to);
                unsafe {
                    std::ptr::copy(ptr, to.as_mut_ptr(), to.len());
                }
            }
            Instr::Reference { to, from } => {
                let ptr: *mut u8 = stack.get_mut(from).as_mut_ptr();
                stack
                    .get_mut(to)
                    .copy_from_slice(&(ptr as usize).to_le_bytes());
            }
            Instr::Move { to, from, size } => {
                let from: *const u8 = stack.get(from).as_ptr();
                let to: *mut u8 = stack.get_mut(to).as_mut_ptr();
                unsafe {
                    std::ptr::copy_nonoverlapping(from, to, size);
                }
            }
            Instr::MoveIndirect { to, from, size } => {
                let from: *const u8 = stack.get(from).as_ptr();

                let mut arr = [0_u8; 8];
                arr.copy_from_slice(stack.get(to));
                let to = usize::from_le_bytes(arr) as *mut u8;

                unsafe {
                    std::ptr::copy_nonoverlapping(from, to, size);
                }
            }
        }
    }
}

/// Returns a u64 from some number of bytes.
fn u64_from_bytes(from: &[u8]) -> u64 {
    assert!(from.len() <= 8);
    let mut bytes = [0_u8; 8];
    bytes[..from.len()].copy_from_slice(from);
    u64::from_le_bytes(bytes)
}
