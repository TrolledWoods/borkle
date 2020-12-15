use crate::ir::{Instr, Routine};
use crate::operators::UnaryOp;
use crate::program::constant::ConstantRef;
use crate::program::Program;

mod stack;

pub use stack::{Stack, StackFrame, StackValue, StackValueMut};

pub fn emit_and_run<'a>(
    thread_context: &mut crate::program::thread_pool::ThreadContext<'a>,
    program: &'a Program,
    locals: crate::locals::LocalVariables,
    expr: &crate::typer::Node,
) -> ConstantRef {
    let mut stack = Stack::new(2048);
    let routine = crate::emit::emit(thread_context, program, locals, expr);
    let result = interp(program, &mut stack, &routine);
    program.insert_buffer(expr.type_(), result.as_ptr())
}

pub fn interp<'a>(
    program: &Program,
    stack: &'a mut Stack,
    routine: &'a Routine,
) -> StackValueMut<'a> {
    let mut stack_frame = stack.stack_frame(&routine.registers);
    interp_internal(program, &mut stack_frame, routine);

    stack_frame.into_value(routine.result)
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
                if unsafe { stack.get(condition).read::<u8>() } == 0 {
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
                let function_ptr = unsafe { stack.get(pointer).read() };

                let mut arg_pointers = Vec::new();
                for &arg in args {
                    arg_pointers.push(stack.get_mut(arg).as_mut_ptr().cast());
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
                let calling: &Routine = unsafe { stack.get(pointer).read() };

                let (mut old_stack, mut new_stack) = stack.split(&calling.registers);

                // Put the arguments on top of the new stack frame
                for (old, new) in args.iter().zip(&calling.registers.locals) {
                    let size = old.type_().size();
                    unsafe {
                        std::ptr::copy_nonoverlapping(
                            old_stack.get(*old).as_ptr(),
                            new_stack.get_mut_from_reg(new).as_mut_ptr(),
                            size,
                        );
                    }
                }

                interp_internal(program, &mut new_stack, calling);

                unsafe {
                    std::ptr::copy_nonoverlapping(
                        new_stack.get(calling.result).as_ptr(),
                        old_stack.get_mut(to).as_mut_ptr(),
                        calling.result.size(),
                    );
                }
            }
            Instr::Constant { to, ref from } => {
                let mut to_ptr = stack.get_mut(to);
                unsafe {
                    std::ptr::copy(from.as_ptr(), to_ptr.as_mut_ptr(), to.size());
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
                    stack.get(a).as_ptr(),
                    stack.get(b).as_ptr(),
                    stack.get_mut(to).as_mut_ptr(),
                );
            },
            Instr::Unary { op, to, from } => match op {
                UnaryOp::Negate => {
                    let from = u64_from_bytes(unsafe {
                        std::slice::from_raw_parts(stack.get(from).as_ptr(), from.size())
                    });
                    let result = from.wrapping_neg();
                    let to_ptr = stack.get_mut(to).as_mut_ptr();
                    unsafe {
                        std::ptr::copy(&result as *const _ as *const _, to_ptr, to.size());
                    }
                }
                UnaryOp::Not => {
                    let from = u64_from_bytes(unsafe {
                        std::slice::from_raw_parts(stack.get(from).as_ptr(), from.size())
                    });
                    let result = !from;
                    let to_ptr = stack.get_mut(to).as_mut_ptr();
                    unsafe {
                        std::ptr::copy(&result as *const _ as *const _, to_ptr, to.size());
                    }
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
                let ptr = unsafe { stack.get(from).read::<*const u8>() };

                let to_ptr = stack.get_mut(to).as_mut_ptr();
                unsafe {
                    std::ptr::copy(ptr, to_ptr, to.size());
                }
            }
            Instr::Reference {
                to,
                from,
                ref offset,
            } => {
                let ptr = stack.get_mut(from).as_mut_ptr();
                unsafe {
                    stack.get_mut(to).write(ptr as usize + offset.offset);
                }
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
                let to = stack.get(to).read::<*mut u8>().add(member.offset);

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
