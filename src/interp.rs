use crate::ir::{Instr, Routine};
use crate::operators::UnaryOp;
use crate::program::Program;

mod stack;

pub use stack::Stack;
use stack::StackFrame;

pub fn interp(program: &Program, stack: &mut Stack, routine: &Routine) -> *const u8 {
    let mut stack_frame = stack.stack_frame(&routine.registers);
    interp_internal(program, &mut stack_frame, routine);

    let ptr = stack_frame.get(routine.result).as_ptr();
    ptr.cast()
}

// The stack frame has to be set up ahead of time here. That is necessary; because
// we need some way to access the result afterwards as well.
fn interp_internal(program: &Program, stack: &mut StackFrame<'_>, routine: &Routine) {
    let mut instr_pointer = 0;
    while instr_pointer < routine.instr.len() {
        let instr = &routine.instr[instr_pointer];
        // println!("Running {:?}", instr);
        match *instr {
            Instr::LabelDefinition(_) => {}
            Instr::JumpIfZero { condition, to } => {
                if stack.get(condition)[0] == 0 {
                    instr_pointer = routine.label_locations[to.0];
                }
            }
            Instr::Jump { to } => {
                instr_pointer = routine.label_locations[to.0];
            }
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
            Instr::Call {
                to,
                pointer,
                ref args,
            } => {
                let mut ptr = [0_u8; 8];
                ptr.copy_from_slice(stack.get(pointer));
                let calling: &Routine = unsafe { std::mem::transmute(usize::from_le_bytes(ptr)) };

                let (mut old_stack, mut new_stack) = stack.split(&calling.registers);

                // Put the arguments on top of the new stack frame
                for (old, new) in args.iter().zip(&calling.registers.locals) {
                    new_stack
                        .get_mut_from_reg(new)
                        .copy_from_slice(old_stack.get(*old));
                }

                interp_internal(program, &mut new_stack, calling);

                old_stack
                    .get_mut(to)
                    .copy_from_slice(new_stack.get(calling.result));
            }
            Instr::Constant { to, ref from } => {
                let to = stack.get_mut(to);
                unsafe {
                    std::ptr::copy(from.as_ptr(), to.as_mut_ptr(), to.len());
                }
            }
            Instr::Binary {
                op,
                to,
                a,
                b,
                left_type,
                right_type,
            } => unsafe {
                op.run(
                    left_type,
                    right_type,
                    stack.get_ptr(a),
                    stack.get_ptr(b),
                    stack.get_mut_ptr(to),
                );
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
                UnaryOp::AutoCast | UnaryOp::Reference | UnaryOp::Dereference => {
                    unreachable!("This operator is supposed to be a special case");
                }
            },
            Instr::Member { to, of, ref member } => unsafe {
                let size = to.size();
                let from: *const u8 = stack.get(of).as_ptr().add(member.offset);
                let to: *mut u8 = stack.get_mut(to).as_mut_ptr();
                std::ptr::copy_nonoverlapping(from, to, size);
            },
            Instr::Dereference { to, from } => {
                let mut arr = [0_u8; 8];
                arr.copy_from_slice(stack.get(from));
                let ptr = usize::from_le_bytes(arr) as *const u8;

                let to = stack.get_mut(to);
                unsafe {
                    std::ptr::copy(ptr, to.as_mut_ptr(), to.len());
                }
            }
            Instr::Reference {
                to,
                from,
                ref offset,
            } => {
                let ptr: *mut u8 = stack.get_mut(from).as_mut_ptr();
                stack
                    .get_mut(to)
                    .copy_from_slice(&(ptr as usize + offset.offset).to_le_bytes());
            }
            Instr::Move {
                to,
                from,
                size,
                ref member,
            } => unsafe {
                let from: *const u8 = stack.get(from).as_ptr();
                let to: *mut u8 = stack.get_mut(to).as_mut_ptr().add(member.offset);
                std::ptr::copy_nonoverlapping(from, to, size);
            },
            Instr::MoveIndirect {
                to,
                from,
                size,
                ref member,
            } => unsafe {
                let from: *const u8 = stack.get(from).as_ptr();

                let mut arr = [0_u8; 8];
                arr.copy_from_slice(stack.get(to));
                let to = (usize::from_le_bytes(arr) as *mut u8).add(member.offset);

                std::ptr::copy_nonoverlapping(from, to, size);
            },
        }

        instr_pointer += 1;
    }
}

/// Returns a u64 from some number of bytes.
fn u64_from_bytes(from: &[u8]) -> u64 {
    assert!(from.len() <= 8);
    let mut bytes = [0_u8; 8];
    bytes[..from.len()].copy_from_slice(from);
    u64::from_le_bytes(bytes)
}
