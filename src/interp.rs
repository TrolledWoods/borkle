use crate::ir::{Instr, Routine, UserDefinedRoutine};
use crate::operators::UnaryOp;
use crate::program::constant::ConstantRef;
use crate::program::{BuiltinFunction, Program};
use crate::types::{BufferRepr, TypeKind};

mod stack;

pub use stack::{Stack, StackFrame, StackValue, StackValueMut};

pub fn emit_and_run<'a>(
    thread_context: &mut crate::thread_pool::ThreadContext<'a>,
    program: &'a Program,
    locals: crate::locals::LocalVariables,
    expr: &crate::typer::Node,
) -> ConstantRef {
    let mut stack = Stack::new(2048);
    // FIXME: This does not take into account calling dependencies
    let (_, routine) = crate::emit::emit(thread_context, program, locals, expr);
    let result = interp(program, &mut stack, &routine);
    program.insert_buffer(expr.type_(), result.as_ptr())
}

pub fn interp<'a>(
    program: &Program,
    stack: &'a mut Stack,
    routine: &'a UserDefinedRoutine,
) -> StackValueMut<'a> {
    let mut stack_frame = stack.stack_frame(&routine.registers);
    interp_internal(program, &mut stack_frame, routine);

    stack_frame.into_value(routine.result)
}

// The stack frame has to be set up ahead of time here. That is necessary; because
// we need some way to access the result afterwards as well.
fn interp_internal(program: &Program, stack: &mut StackFrame<'_>, routine: &UserDefinedRoutine) {
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
            Instr::Call {
                to,
                pointer,
                ref args,
            } => {
                let calling = program
                    .get_routine(unsafe { stack.get(pointer).read() })
                    .expect("Invalid function pointer. There are two reasons this could happen; you bit_casted some number into a function pointer, or there is a bug in the compilers dependency system.");

                match &*calling {
                    Routine::Builtin(BuiltinFunction::StdoutWrite) => unsafe {
                        use std::io::Write;
                        let buffer = stack.get(args[0]).read::<BufferRepr>();

                        let output = std::io::stdout()
                            .write(std::slice::from_raw_parts(buffer.ptr, buffer.length))
                            .unwrap_or(0);

                        stack.get_mut(to).write::<usize>(output);
                    },
                    Routine::Builtin(BuiltinFunction::StdoutFlush) => {
                        use std::io::Write;
                        let _ = std::io::stdout().lock().flush();
                    }
                    Routine::Builtin(BuiltinFunction::StdinGetLine) => unsafe {
                        let mut string = String::new();
                        let _ = std::io::stdin().read_line(&mut string);

                        let string_bytes = string.into_bytes().into_boxed_slice();

                        let repr = BufferRepr {
                            length: string_bytes.len(),
                            ptr: Box::into_raw(string_bytes).cast(),
                        };
                        stack.get_mut(to).write(repr);
                    },
                    Routine::Builtin(BuiltinFunction::Alloc) => unsafe {
                        use std::alloc::{alloc, Layout};
                        let ptr = alloc(Layout::from_size_align_unchecked(
                            stack.get(args[0]).read::<usize>(),
                            8,
                        ));
                        stack.get_mut(to).write(ptr);
                    },
                    Routine::Builtin(BuiltinFunction::Dealloc) => unsafe {
                        use std::alloc::{dealloc, Layout};
                        let buffer = stack.get(args[0]).read::<BufferRepr>();
                        dealloc(
                            buffer.ptr,
                            Layout::from_size_align_unchecked(buffer.length, 8),
                        );
                    },
                    Routine::Builtin(BuiltinFunction::MemCopy) => unsafe {
                        std::ptr::copy(
                            stack.get(args[0]).read::<*const u8>(),
                            stack.get_mut(args[1]).read::<*mut u8>(),
                            stack.get(args[2]).read::<usize>(),
                        );
                    },
                    Routine::Builtin(BuiltinFunction::MemCopyNonOverlapping) => unsafe {
                        std::ptr::copy_nonoverlapping(
                            stack.get(args[0]).read::<*const u8>(),
                            stack.get_mut(args[1]).read::<*mut u8>(),
                            stack.get(args[2]).read::<usize>(),
                        );
                    },
                    Routine::UserDefined(calling) => {
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
                }
            }
            Instr::Increment { value } => {
                let incr_amount = match value.type_().kind() {
                    TypeKind::Int(_) => 1,
                    TypeKind::Reference(inner) => inner.size() as u64,
                    _ => unreachable!(),
                };

                let size = value.size();

                let mut value = stack.get_mut(value);
                let result = unsafe { value.read::<u64>() } + incr_amount;
                unsafe {
                    std::ptr::copy(result.to_le_bytes().as_ptr(), value.as_mut_ptr(), size);
                }
            }
            Instr::Binary { op, to, a, b } => unsafe {
                op.run(
                    a.type_(),
                    b.type_(),
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
                    // FIXME; Make this more efficient, this is just a hack to get it working
                    if *from.type_().kind() == TypeKind::Bool {
                        let from = unsafe { stack.get(from).read::<bool>() };
                        let result = !from;
                        unsafe {
                            stack.get_mut(to).write(result);
                        }
                    } else {
                        let from = u64_from_bytes(unsafe {
                            std::slice::from_raw_parts(stack.get(from).as_ptr(), from.size())
                        });
                        let result = !from;
                        let to_ptr = stack.get_mut(to).as_mut_ptr();
                        unsafe {
                            std::ptr::copy(&result as *const _ as *const _, to_ptr, to.size());
                        }
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
            Instr::PointerToMemberOfPointer { to, of, ref member } => unsafe {
                let from: *const u8 =
                    (*stack.get(of).as_ptr().cast::<*const u8>()).add(member.offset);
                let to: *mut u8 = stack.get_mut(to).as_mut_ptr();
                *to.cast::<*const u8>() = from;
            },
            Instr::Dereference { to, from } => {
                let ptr = unsafe { stack.get(from).read::<*const u8>() };

                let to_ptr = stack.get_mut(to).as_mut_ptr();
                unsafe {
                    std::ptr::copy(ptr, to_ptr, to.size());
                }
            }
            Instr::PointerToMemberOfValue {
                to,
                from,
                ref offset,
            } => {
                let ptr = stack.get_mut(from).as_mut_ptr();
                unsafe {
                    stack.get_mut(to).write(ptr as usize + offset.offset);
                }
            }
            Instr::MoveToMemberOfValue {
                to,
                from,
                size,
                ref member,
            } => unsafe {
                let from: *const u8 = stack.get(from).as_ptr();
                let to: *mut u8 = stack.get_mut(to).as_mut_ptr().add(member.offset);
                std::ptr::copy_nonoverlapping(from, to, size);
            },
            Instr::MoveToMemberOfPointer {
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
