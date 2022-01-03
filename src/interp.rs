use crate::ir::{Instr, Routine, UserDefinedRoutine, NumberType};
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::constant::ConstantRef;
use crate::program::{BuiltinFunction, Program};
use crate::types::{BufferRepr, TypeKind};
use crate::type_infer::{TypeSystem, ValueId as TypeId, AstVariantId};
use crate::typer::AdditionalInfo;

mod stack;

pub use stack::{Stack, StackFrame, StackValue, StackValueMut};

pub fn emit_and_run<'a>(
    thread_context: &mut crate::thread_pool::ThreadContext<'a>,
    program: &'a Program,
    locals: &mut crate::locals::LocalVariables,
    types: &mut TypeSystem,
    ast: &crate::typer::Ast,
    additional_info: &AdditionalInfo,
    node: crate::ast::NodeId,
    variant_id: AstVariantId,
    call_stack: &mut Vec<Location>,
) -> Result<ConstantRef, Box<[Location]>> {
    // FIXME: This does not take into account calling dependencies
    let (_, routine) = crate::emit::emit(
        thread_context,
        program,
        locals,
        types,
        ast,
        additional_info,
        node,
        variant_id,
    );
    let mut stack = Stack::new(2048);
    let result = interp(program, &mut stack, &routine, call_stack)?;
    Ok(program.insert_buffer(types.value_to_compiler_type(TypeId::Node(variant_id, node)), result.as_ptr()))
}

pub fn interp<'a>(
    program: &Program,
    stack: &'a mut Stack,
    routine: &'a UserDefinedRoutine,
    call_stack: &mut Vec<Location>,
) -> Result<StackValueMut<'a>, Box<[Location]>> {
    let mut stack_frame = stack.stack_frame(&routine.stack);
    interp_internal(program, &mut stack_frame, routine, call_stack)?;

    Ok(stack_frame.into_value(routine.result))
}

// The stack frame has to be set up ahead of time here. That is necessary; because
// we need some way to access the result afterwards as well.
fn interp_internal(program: &Program, stack: &mut StackFrame<'_>, routine: &UserDefinedRoutine, call_stack: &mut Vec<Location>) -> Result<(), Box<[Location]>> {
    let mut instr_pointer = 0;
    while instr_pointer < routine.instr.len() {
        let instr = &routine.instr[instr_pointer];
        
        // let mut out = String::new();
        // crate::backend::ir::print_instr(&mut out, instr);
        // print!("{}", out);

        let mut pause_instr_ptr = false;

        match *instr {
            Instr::LabelDefinition(_) => {}
            Instr::DebugLocation { .. } => {}
            Instr::JumpIfZero { condition, to } => {
                if unsafe { stack.get(condition).read::<u8>() } == 0 {
                    instr_pointer = routine.label_locations[to.0];
                    pause_instr_ptr = true;
                }
            }
            Instr::SetToZero { to_ptr, size } => {
                let ptr = stack.get_mut(to_ptr).as_mut_ptr();
                unsafe {
                    std::ptr::write_bytes(ptr, 0, size);
                }
            }
            Instr::Jump { to } => {
                instr_pointer = routine.label_locations[to.0];
                pause_instr_ptr = true;
            }
            Instr::Call {
                to,
                pointer,
                ref args,
                loc,
            } => {
                call_stack.push(loc);

                let calling = program
                    .get_routine(unsafe { stack.get(pointer).read() })
                    .expect("Invalid function pointer. There are two reasons this could happen; you bit_casted some number into a function pointer, or there is a bug in the compilers dependency system.");

                match &*calling {
                    Routine::Builtin(BuiltinFunction::Assert) => unsafe {
                        let condition = stack.get(args[0].0).read::<u8>();
                        if condition == 0 {
                            return Err(std::mem::take(call_stack).into_boxed_slice());
                        }
                    }
                    Routine::Builtin(BuiltinFunction::StdoutWrite) => unsafe {
                        use std::io::Write;
                        let buffer = stack.get(args[0].0).read::<BufferRepr>();

                        let output = std::io::stdout()
                            .write(std::slice::from_raw_parts(buffer.ptr, buffer.length))
                            .unwrap_or(0);

                        stack.get_mut(to.0).write::<usize>(output);
                    },
                    Routine::Builtin(BuiltinFunction::StdoutFlush) => {
                        use std::io::Write;
                        let _ = std::io::stdout().lock().flush();
                    }
                    Routine::Builtin(BuiltinFunction::StdinRead) => unsafe {
                        let buffer = stack.get(args[0].0).read::<BufferRepr>();
                        let slice = std::slice::from_raw_parts_mut(buffer.ptr, buffer.length);

                        use std::io::Read;
                        let num_read = std::io::stdin().lock().read(slice).unwrap();
                        stack.get_mut(to.0).write(num_read);
                    },
                    Routine::Builtin(BuiltinFunction::Alloc) => unsafe {
                        use std::alloc::{alloc, Layout};
                        let ptr = alloc(Layout::from_size_align_unchecked(
                            stack.get(args[0].0).read::<usize>(),
                            8,
                        ));
                        stack.get_mut(to.0).write(ptr);
                    },
                    Routine::Builtin(BuiltinFunction::Dealloc) => unsafe {
                        use std::alloc::{dealloc, Layout};
                        let buffer = stack.get(args[0].0).read::<BufferRepr>();
                        dealloc(
                            buffer.ptr,
                            Layout::from_size_align_unchecked(buffer.length, 8),
                        );
                    },
                    Routine::Builtin(BuiltinFunction::MemCopy) => unsafe {
                        std::ptr::copy(
                            stack.get(args[0].0).read::<*const u8>(),
                            stack.get_mut(args[1].0).read::<*mut u8>(),
                            stack.get(args[2].0).read::<usize>(),
                        );
                    },
                    Routine::Builtin(BuiltinFunction::MemCopyNonOverlapping) => unsafe {
                        std::ptr::copy_nonoverlapping(
                            stack.get(args[0].0).read::<*const u8>(),
                            stack.get_mut(args[1].0).read::<*mut u8>(),
                            stack.get(args[2].0).read::<usize>(),
                        );
                    },
                    Routine::UserDefined(calling) => {
                        let (mut old_stack, mut new_stack) = stack.split(&calling.stack);

                        // Put the arguments on top of the new stack frame
                        for (&(old, old_layout), new) in args.iter().zip(&calling.stack.values) {
                            if old_layout.size > 0 {
                                unsafe {
                                    std::ptr::copy_nonoverlapping(
                                        old_stack.get(old).as_ptr(),
                                        new_stack.get_mut(new.value()).as_mut_ptr(),
                                        old_layout.size,
                                    );
                                }
                            }
                        }

                        interp_internal(program, &mut new_stack, calling, call_stack)?;

                        if to.1.size > 0 {
                            unsafe {
                                std::ptr::copy_nonoverlapping(
                                    new_stack.get(calling.result).as_ptr(),
                                    old_stack.get_mut(to.0).as_mut_ptr(),
                                    to.1.size,
                                );
                            }
                        }
                    }
                }

                call_stack.pop();
            }
            Instr::IncrPtr { to, amount, scale } => unsafe {
                let amount = stack.get(amount).read::<usize>();
                let to = stack.get_mut(to);
                let new_ptr = to.read::<usize>() + amount * scale;
                to.write(new_ptr);
            },
            Instr::BinaryImm { op, to, a, b, type_ } => unsafe {
                run_binary_op(op, stack.get_mut(to).as_mut_ptr(), stack.get(a).as_ptr(), &b as *const _ as *const _, type_);
            },
            Instr::Binary { op, to, a, b, type_ } => unsafe {
                run_binary_op(op, stack.get_mut(to).as_mut_ptr(), stack.get(a).as_ptr(), stack.get(b).as_ptr(), type_);
            },
            Instr::Unary { op, to, from, type_ } => unsafe {
                run_unary_op(op, stack.get_mut(to).as_mut_ptr(), stack.get(from).as_ptr(), type_);
            },
            Instr::MoveImm { to, from, size } => unsafe {
                let to: *mut u8 = stack.get_mut(to).as_mut_ptr();
                std::ptr::copy_nonoverlapping(from.as_ptr(), to, size);
            },
            Instr::Move { to, from, size } => unsafe {
                let from: *const u8 = stack.get(from).as_ptr();
                let to: *mut u8 = stack.get_mut(to).as_mut_ptr();
                std::ptr::copy_nonoverlapping(from, to, size);
            },
            Instr::RefGlobal { to_ptr, global } => {
                let to_ptr = stack.get_mut(to_ptr).as_mut_ptr().cast::<*const u8>();
                let from_ptr = global.as_ptr();
                unsafe {
                    *to_ptr = from_ptr;
                }
            }
            Instr::StackPtr { to, take_pointer_to } => {
                let to_ptr = stack.get_mut(to).as_mut_ptr().cast::<*const u8>();
                let from_ptr = stack.get(take_pointer_to).as_ptr();
                unsafe {
                    *to_ptr = from_ptr;
                }
            }
            Instr::IndirectMove { to_ptr, from, size } => {
                let to_ptr = unsafe { stack.get_mut(to_ptr).read::<*mut u8>() };
                let from_ptr = stack.get(from).as_ptr();
                unsafe {
                    std::ptr::copy(from_ptr, to_ptr, size);
                }
            }
            Instr::Dereference { to, from_ptr, size } => {
                let ptr = unsafe { stack.get(from_ptr).read::<*const u8>() };

                let to_ptr = stack.get_mut(to).as_mut_ptr();
                unsafe {
                    std::ptr::copy(ptr, to_ptr, size);
                }
            }
            Instr::ConvertNum {
                to,
                from,
                to_number,
                from_number,
            } => unsafe {
                convert_num(stack.get_mut(to).as_mut_ptr(), stack.get(from).as_ptr(), to_number, from_number);
            },
        }

        if !pause_instr_ptr {
            instr_pointer += 1;
        }
    }

    // println!("\tRET");

    Ok(())
}

pub unsafe fn run_unary_op(op: UnaryOp, result: *mut u8, a: *const u8, number: NumberType) {
    match (op, number) {
        (UnaryOp::Not, NumberType::U8)  => *result.cast::<u8 >() = !*a.cast::<u8 >(),
        (UnaryOp::Not, NumberType::U16) => *result.cast::<u16>() = !*a.cast::<u16>(),
        (UnaryOp::Not, NumberType::U32) => *result.cast::<u32>() = !*a.cast::<u32>(),
        (UnaryOp::Not, NumberType::U64) => *result.cast::<u64>() = !*a.cast::<u64>(),
        (UnaryOp::Not, NumberType::I8)  => *result.cast::<i8 >() = !*a.cast::<i8 >(),
        (UnaryOp::Not, NumberType::I16) => *result.cast::<i16>() = !*a.cast::<i16>(),
        (UnaryOp::Not, NumberType::I32) => *result.cast::<i32>() = !*a.cast::<i32>(),
        (UnaryOp::Not, NumberType::I64) => *result.cast::<i64>() = !*a.cast::<i64>(),

        (UnaryOp::Negate, NumberType::I8)  => *result.cast::<i8 >() = -*a.cast::<i8 >(),
        (UnaryOp::Negate, NumberType::I16) => *result.cast::<i16>() = -*a.cast::<i16>(),
        (UnaryOp::Negate, NumberType::I32) => *result.cast::<i32>() = -*a.cast::<i32>(),
        (UnaryOp::Negate, NumberType::I64) => *result.cast::<i64>() = -*a.cast::<i64>(),
        (UnaryOp::Negate, NumberType::F32) => *result.cast::<f32>() = -*a.cast::<f32>(),
        (UnaryOp::Negate, NumberType::F64) => *result.cast::<f64>() = -*a.cast::<f64>(),

        _ => unreachable!(),
    }
}

pub unsafe fn convert_num(to: *mut u8, from: *const u8, to_num: NumberType, from_num: NumberType) {
    let middle = match from_num {
        NumberType::U8  => *from.cast::<u8 >() as i128,
        NumberType::U16 => *from.cast::<u16>() as i128,
        NumberType::U32 => *from.cast::<u32>() as i128,
        NumberType::U64 => *from.cast::<u64>() as i128,
        NumberType::I8  => *from.cast::<i8 >() as i128,
        NumberType::I16 => *from.cast::<i16>() as i128,
        NumberType::I32 => *from.cast::<i32>() as i128,
        NumberType::I64 => *from.cast::<i64>() as i128,
        NumberType::F32 => *from.cast::<f32>() as i128,
        NumberType::F64 => *from.cast::<f64>() as i128,
    };

    match to_num {
        NumberType::U8  => *to.cast::<u8 >() = middle as _,
        NumberType::U16 => *to.cast::<u16>() = middle as _,
        NumberType::U32 => *to.cast::<u32>() = middle as _,
        NumberType::U64 => *to.cast::<u64>() = middle as _,
        NumberType::I8  => *to.cast::<i8 >() = middle as _,
        NumberType::I16 => *to.cast::<i16>() = middle as _,
        NumberType::I32 => *to.cast::<i32>() = middle as _,
        NumberType::I64 => *to.cast::<i64>() = middle as _,
        NumberType::F32 => *to.cast::<f32>() = middle as _,
        NumberType::F64 => *to.cast::<f64>() = middle as _,
    }
}

pub unsafe fn run_binary_op(op: BinaryOp, result: *mut u8, a: *const u8, b: *const u8, number: NumberType) {
    match (op, number) {
        // @TODO: These should give an assert failure if failing, and not fail in rust
        (BinaryOp::ShiftLeft, NumberType::U8)  => *result.cast::<u8 >() = *a.cast::<u8 >() << *b.cast::<u8 >(),
        (BinaryOp::ShiftLeft, NumberType::U16) => *result.cast::<u16>() = *a.cast::<u16>() << *b.cast::<u16>(),
        (BinaryOp::ShiftLeft, NumberType::U32) => *result.cast::<u32>() = *a.cast::<u32>() << *b.cast::<u32>(),
        (BinaryOp::ShiftLeft, NumberType::U64) => *result.cast::<u64>() = *a.cast::<u64>() << *b.cast::<u64>(),
        (BinaryOp::ShiftLeft, NumberType::I8)  => *result.cast::<i8 >() = *a.cast::<i8 >() << *b.cast::<i8 >(),
        (BinaryOp::ShiftLeft, NumberType::I16) => *result.cast::<i16>() = *a.cast::<i16>() << *b.cast::<i16>(),
        (BinaryOp::ShiftLeft, NumberType::I32) => *result.cast::<i32>() = *a.cast::<i32>() << *b.cast::<i32>(),
        (BinaryOp::ShiftLeft, NumberType::I64) => *result.cast::<i64>() = *a.cast::<i64>() << *b.cast::<i64>(),

        (BinaryOp::ShiftRight, NumberType::U8)  => *result.cast::<u8 >() = *a.cast::<u8 >() >> *b.cast::<u8 >(),
        (BinaryOp::ShiftRight, NumberType::U16) => *result.cast::<u16>() = *a.cast::<u16>() >> *b.cast::<u16>(),
        (BinaryOp::ShiftRight, NumberType::U32) => *result.cast::<u32>() = *a.cast::<u32>() >> *b.cast::<u32>(),
        (BinaryOp::ShiftRight, NumberType::U64) => *result.cast::<u64>() = *a.cast::<u64>() >> *b.cast::<u64>(),
        (BinaryOp::ShiftRight, NumberType::I8)  => *result.cast::<i8 >() = *a.cast::<i8 >() >> *b.cast::<i8 >(),
        (BinaryOp::ShiftRight, NumberType::I16) => *result.cast::<i16>() = *a.cast::<i16>() >> *b.cast::<i16>(),
        (BinaryOp::ShiftRight, NumberType::I32) => *result.cast::<i32>() = *a.cast::<i32>() >> *b.cast::<i32>(),
        (BinaryOp::ShiftRight, NumberType::I64) => *result.cast::<i64>() = *a.cast::<i64>() >> *b.cast::<i64>(),

        (BinaryOp::BitAnd, NumberType::U8)  => *result.cast::<u8 >() = *a.cast::<u8 >() & *b.cast::<u8 >(),
        (BinaryOp::BitAnd, NumberType::U16) => *result.cast::<u16>() = *a.cast::<u16>() & *b.cast::<u16>(),
        (BinaryOp::BitAnd, NumberType::U32) => *result.cast::<u32>() = *a.cast::<u32>() & *b.cast::<u32>(),
        (BinaryOp::BitAnd, NumberType::U64) => *result.cast::<u64>() = *a.cast::<u64>() & *b.cast::<u64>(),
        (BinaryOp::BitAnd, NumberType::I8)  => *result.cast::<i8 >() = *a.cast::<i8 >() & *b.cast::<i8 >(),
        (BinaryOp::BitAnd, NumberType::I16) => *result.cast::<i16>() = *a.cast::<i16>() & *b.cast::<i16>(),
        (BinaryOp::BitAnd, NumberType::I32) => *result.cast::<i32>() = *a.cast::<i32>() & *b.cast::<i32>(),
        (BinaryOp::BitAnd, NumberType::I64) => *result.cast::<i64>() = *a.cast::<i64>() & *b.cast::<i64>(),

        (BinaryOp::BitOr, NumberType::U8)  => *result.cast::<u8 >() = *a.cast::<u8 >() | *b.cast::<u8 >(),
        (BinaryOp::BitOr, NumberType::U16) => *result.cast::<u16>() = *a.cast::<u16>() | *b.cast::<u16>(),
        (BinaryOp::BitOr, NumberType::U32) => *result.cast::<u32>() = *a.cast::<u32>() | *b.cast::<u32>(),
        (BinaryOp::BitOr, NumberType::U64) => *result.cast::<u64>() = *a.cast::<u64>() | *b.cast::<u64>(),
        (BinaryOp::BitOr, NumberType::I8)  => *result.cast::<i8 >() = *a.cast::<i8 >() | *b.cast::<i8 >(),
        (BinaryOp::BitOr, NumberType::I16) => *result.cast::<i16>() = *a.cast::<i16>() | *b.cast::<i16>(),
        (BinaryOp::BitOr, NumberType::I32) => *result.cast::<i32>() = *a.cast::<i32>() | *b.cast::<i32>(),
        (BinaryOp::BitOr, NumberType::I64) => *result.cast::<i64>() = *a.cast::<i64>() | *b.cast::<i64>(),

        (BinaryOp::Add, NumberType::U8)  => *result.cast::<u8 >() = (*a.cast::<u8 >()).wrapping_add(*b.cast::<u8 >()),
        (BinaryOp::Add, NumberType::U16) => *result.cast::<u16>() = (*a.cast::<u16>()).wrapping_add(*b.cast::<u16>()),
        (BinaryOp::Add, NumberType::U32) => *result.cast::<u32>() = (*a.cast::<u32>()).wrapping_add(*b.cast::<u32>()),
        (BinaryOp::Add, NumberType::U64) => *result.cast::<u64>() = (*a.cast::<u64>()).wrapping_add(*b.cast::<u64>()),
        (BinaryOp::Add, NumberType::I8)  => *result.cast::<i8 >() = (*a.cast::<i8 >()).wrapping_add(*b.cast::<i8 >()),
        (BinaryOp::Add, NumberType::I16) => *result.cast::<i16>() = (*a.cast::<i16>()).wrapping_add(*b.cast::<i16>()),
        (BinaryOp::Add, NumberType::I32) => *result.cast::<i32>() = (*a.cast::<i32>()).wrapping_add(*b.cast::<i32>()),
        (BinaryOp::Add, NumberType::I64) => *result.cast::<i64>() = (*a.cast::<i64>()).wrapping_add(*b.cast::<i64>()),
        (BinaryOp::Add, NumberType::F32) => *result.cast::<f32>() = *a.cast::<f32>() + *b.cast::<f32>(),
        (BinaryOp::Add, NumberType::F64) => *result.cast::<f64>() = *a.cast::<f64>() + *b.cast::<f64>(),

        (BinaryOp::Sub, NumberType::U8)  => *result.cast::<u8 >() = (*a.cast::<u8 >()).wrapping_sub(*b.cast::<u8 >()),
        (BinaryOp::Sub, NumberType::U16) => *result.cast::<u16>() = (*a.cast::<u16>()).wrapping_sub(*b.cast::<u16>()),
        (BinaryOp::Sub, NumberType::U32) => *result.cast::<u32>() = (*a.cast::<u32>()).wrapping_sub(*b.cast::<u32>()),
        (BinaryOp::Sub, NumberType::U64) => *result.cast::<u64>() = (*a.cast::<u64>()).wrapping_sub(*b.cast::<u64>()),
        (BinaryOp::Sub, NumberType::I8)  => *result.cast::<i8 >() = (*a.cast::<i8 >()).wrapping_sub(*b.cast::<i8 >()),
        (BinaryOp::Sub, NumberType::I16) => *result.cast::<i16>() = (*a.cast::<i16>()).wrapping_sub(*b.cast::<i16>()),
        (BinaryOp::Sub, NumberType::I32) => *result.cast::<i32>() = (*a.cast::<i32>()).wrapping_sub(*b.cast::<i32>()),
        (BinaryOp::Sub, NumberType::I64) => *result.cast::<i64>() = (*a.cast::<i64>()).wrapping_sub(*b.cast::<i64>()),
        (BinaryOp::Sub, NumberType::F32) => *result.cast::<f32>() = *a.cast::<f32>() - *b.cast::<f32>(),
        (BinaryOp::Sub, NumberType::F64) => *result.cast::<f64>() = *a.cast::<f64>() - *b.cast::<f64>(),

        (BinaryOp::Mult, NumberType::U8)  => *result.cast::<u8 >() = (*a.cast::<u8 >()).wrapping_mul(*b.cast::<u8 >()),
        (BinaryOp::Mult, NumberType::U16) => *result.cast::<u16>() = (*a.cast::<u16>()).wrapping_mul(*b.cast::<u16>()),
        (BinaryOp::Mult, NumberType::U32) => *result.cast::<u32>() = (*a.cast::<u32>()).wrapping_mul(*b.cast::<u32>()),
        (BinaryOp::Mult, NumberType::U64) => *result.cast::<u64>() = (*a.cast::<u64>()).wrapping_mul(*b.cast::<u64>()),
        (BinaryOp::Mult, NumberType::I8)  => *result.cast::<i8 >() = (*a.cast::<i8 >()).wrapping_mul(*b.cast::<i8 >()),
        (BinaryOp::Mult, NumberType::I16) => *result.cast::<i16>() = (*a.cast::<i16>()).wrapping_mul(*b.cast::<i16>()),
        (BinaryOp::Mult, NumberType::I32) => *result.cast::<i32>() = (*a.cast::<i32>()).wrapping_mul(*b.cast::<i32>()),
        (BinaryOp::Mult, NumberType::I64) => *result.cast::<i64>() = (*a.cast::<i64>()).wrapping_mul(*b.cast::<i64>()),
        (BinaryOp::Mult, NumberType::F32) => *result.cast::<f32>() = *a.cast::<f32>() * *b.cast::<f32>(),
        (BinaryOp::Mult, NumberType::F64) => *result.cast::<f64>() = *a.cast::<f64>() * *b.cast::<f64>(),

        // TODO: Should these cause assert failures?
        (BinaryOp::Div, NumberType::U8)  => *result.cast::<u8 >() = (*a.cast::<u8 >()).checked_div(*b.cast::<u8 >()).unwrap_or(0),
        (BinaryOp::Div, NumberType::U16) => *result.cast::<u16>() = (*a.cast::<u16>()).checked_div(*b.cast::<u16>()).unwrap_or(0),
        (BinaryOp::Div, NumberType::U32) => *result.cast::<u32>() = (*a.cast::<u32>()).checked_div(*b.cast::<u32>()).unwrap_or(0),
        (BinaryOp::Div, NumberType::U64) => *result.cast::<u64>() = (*a.cast::<u64>()).checked_div(*b.cast::<u64>()).unwrap_or(0),
        (BinaryOp::Div, NumberType::I8)  => *result.cast::<i8 >() = (*a.cast::<i8 >()).checked_div(*b.cast::<i8 >()).unwrap_or(0),
        (BinaryOp::Div, NumberType::I16) => *result.cast::<i16>() = (*a.cast::<i16>()).checked_div(*b.cast::<i16>()).unwrap_or(0),
        (BinaryOp::Div, NumberType::I32) => *result.cast::<i32>() = (*a.cast::<i32>()).checked_div(*b.cast::<i32>()).unwrap_or(0),
        (BinaryOp::Div, NumberType::I64) => *result.cast::<i64>() = (*a.cast::<i64>()).checked_div(*b.cast::<i64>()).unwrap_or(0),
        (BinaryOp::Div, NumberType::F32) => *result.cast::<f32>() = *a.cast::<f32>() / *b.cast::<f32>(),
        (BinaryOp::Div, NumberType::F64) => *result.cast::<f64>() = *a.cast::<f64>() / *b.cast::<f64>(),

        (BinaryOp::Modulo, NumberType::U8)  => *result.cast::<u8 >() = (*a.cast::<u8 >()).checked_rem(*b.cast::<u8 >()).unwrap_or(0),
        (BinaryOp::Modulo, NumberType::U16) => *result.cast::<u16>() = (*a.cast::<u16>()).checked_rem(*b.cast::<u16>()).unwrap_or(0),
        (BinaryOp::Modulo, NumberType::U32) => *result.cast::<u32>() = (*a.cast::<u32>()).checked_rem(*b.cast::<u32>()).unwrap_or(0),
        (BinaryOp::Modulo, NumberType::U64) => *result.cast::<u64>() = (*a.cast::<u64>()).checked_rem(*b.cast::<u64>()).unwrap_or(0),
        (BinaryOp::Modulo, NumberType::I8)  => *result.cast::<i8 >() = (*a.cast::<i8 >()).checked_rem(*b.cast::<i8 >()).unwrap_or(0),
        (BinaryOp::Modulo, NumberType::I16) => *result.cast::<i16>() = (*a.cast::<i16>()).checked_rem(*b.cast::<i16>()).unwrap_or(0),
        (BinaryOp::Modulo, NumberType::I32) => *result.cast::<i32>() = (*a.cast::<i32>()).checked_rem(*b.cast::<i32>()).unwrap_or(0),
        (BinaryOp::Modulo, NumberType::I64) => *result.cast::<i64>() = (*a.cast::<i64>()).checked_rem(*b.cast::<i64>()).unwrap_or(0),
        (BinaryOp::Modulo, NumberType::F32) => *result.cast::<f32>() = *a.cast::<f32>() / *b.cast::<f32>(),
        (BinaryOp::Modulo, NumberType::F64) => *result.cast::<f64>() = *a.cast::<f64>() / *b.cast::<f64>(),

        (BinaryOp::Equals, NumberType::U8)  => *result.cast::<bool>() = *a.cast::<u8 >() == *b.cast::<u8 >(),
        (BinaryOp::Equals, NumberType::U16) => *result.cast::<bool>() = *a.cast::<u16>() == *b.cast::<u16>(),
        (BinaryOp::Equals, NumberType::U32) => *result.cast::<bool>() = *a.cast::<u32>() == *b.cast::<u32>(),
        (BinaryOp::Equals, NumberType::U64) => *result.cast::<bool>() = *a.cast::<u64>() == *b.cast::<u64>(),
        (BinaryOp::Equals, NumberType::I8)  => *result.cast::<bool>() = *a.cast::<i8 >() == *b.cast::<i8 >(),
        (BinaryOp::Equals, NumberType::I16) => *result.cast::<bool>() = *a.cast::<i16>() == *b.cast::<i16>(),
        (BinaryOp::Equals, NumberType::I32) => *result.cast::<bool>() = *a.cast::<i32>() == *b.cast::<i32>(),
        (BinaryOp::Equals, NumberType::I64) => *result.cast::<bool>() = *a.cast::<i64>() == *b.cast::<i64>(),
        (BinaryOp::Equals, NumberType::F32) => *result.cast::<bool>() = *a.cast::<f32>() == *b.cast::<f32>(),
        (BinaryOp::Equals, NumberType::F64) => *result.cast::<bool>() = *a.cast::<f64>() == *b.cast::<f64>(),

        (BinaryOp::NotEquals, NumberType::U8)  => *result.cast::<bool>() = *a.cast::<u8 >() != *b.cast::<u8 >(),
        (BinaryOp::NotEquals, NumberType::U16) => *result.cast::<bool>() = *a.cast::<u16>() != *b.cast::<u16>(),
        (BinaryOp::NotEquals, NumberType::U32) => *result.cast::<bool>() = *a.cast::<u32>() != *b.cast::<u32>(),
        (BinaryOp::NotEquals, NumberType::U64) => *result.cast::<bool>() = *a.cast::<u64>() != *b.cast::<u64>(),
        (BinaryOp::NotEquals, NumberType::I8)  => *result.cast::<bool>() = *a.cast::<i8 >() != *b.cast::<i8 >(),
        (BinaryOp::NotEquals, NumberType::I16) => *result.cast::<bool>() = *a.cast::<i16>() != *b.cast::<i16>(),
        (BinaryOp::NotEquals, NumberType::I32) => *result.cast::<bool>() = *a.cast::<i32>() != *b.cast::<i32>(),
        (BinaryOp::NotEquals, NumberType::I64) => *result.cast::<bool>() = *a.cast::<i64>() != *b.cast::<i64>(),
        (BinaryOp::NotEquals, NumberType::F32) => *result.cast::<bool>() = *a.cast::<f32>() != *b.cast::<f32>(),
        (BinaryOp::NotEquals, NumberType::F64) => *result.cast::<bool>() = *a.cast::<f64>() != *b.cast::<f64>(),

        (BinaryOp::LessThan, NumberType::U8)  => *result.cast::<bool>() = *a.cast::<u8 >() < *b.cast::<u8 >(),
        (BinaryOp::LessThan, NumberType::U16) => *result.cast::<bool>() = *a.cast::<u16>() < *b.cast::<u16>(),
        (BinaryOp::LessThan, NumberType::U32) => *result.cast::<bool>() = *a.cast::<u32>() < *b.cast::<u32>(),
        (BinaryOp::LessThan, NumberType::U64) => *result.cast::<bool>() = *a.cast::<u64>() < *b.cast::<u64>(),
        (BinaryOp::LessThan, NumberType::I8)  => *result.cast::<bool>() = *a.cast::<i8 >() < *b.cast::<i8 >(),
        (BinaryOp::LessThan, NumberType::I16) => *result.cast::<bool>() = *a.cast::<i16>() < *b.cast::<i16>(),
        (BinaryOp::LessThan, NumberType::I32) => *result.cast::<bool>() = *a.cast::<i32>() < *b.cast::<i32>(),
        (BinaryOp::LessThan, NumberType::I64) => *result.cast::<bool>() = *a.cast::<i64>() < *b.cast::<i64>(),
        (BinaryOp::LessThan, NumberType::F32) => *result.cast::<bool>() = *a.cast::<f32>() < *b.cast::<f32>(),
        (BinaryOp::LessThan, NumberType::F64) => *result.cast::<bool>() = *a.cast::<f64>() < *b.cast::<f64>(),

        (BinaryOp::LessThanEquals, NumberType::U8)  => *result.cast::<bool>() = *a.cast::<u8 >() <= *b.cast::<u8 >(),
        (BinaryOp::LessThanEquals, NumberType::U16) => *result.cast::<bool>() = *a.cast::<u16>() <= *b.cast::<u16>(),
        (BinaryOp::LessThanEquals, NumberType::U32) => *result.cast::<bool>() = *a.cast::<u32>() <= *b.cast::<u32>(),
        (BinaryOp::LessThanEquals, NumberType::U64) => *result.cast::<bool>() = *a.cast::<u64>() <= *b.cast::<u64>(),
        (BinaryOp::LessThanEquals, NumberType::I8)  => *result.cast::<bool>() = *a.cast::<i8 >() <= *b.cast::<i8 >(),
        (BinaryOp::LessThanEquals, NumberType::I16) => *result.cast::<bool>() = *a.cast::<i16>() <= *b.cast::<i16>(),
        (BinaryOp::LessThanEquals, NumberType::I32) => *result.cast::<bool>() = *a.cast::<i32>() <= *b.cast::<i32>(),
        (BinaryOp::LessThanEquals, NumberType::I64) => *result.cast::<bool>() = *a.cast::<i64>() <= *b.cast::<i64>(),
        (BinaryOp::LessThanEquals, NumberType::F32) => *result.cast::<bool>() = *a.cast::<f32>() <= *b.cast::<f32>(),
        (BinaryOp::LessThanEquals, NumberType::F64) => *result.cast::<bool>() = *a.cast::<f64>() <= *b.cast::<f64>(),

        (BinaryOp::LargerThan, NumberType::U8)  => *result.cast::<bool>() = *a.cast::<u8 >() > *b.cast::<u8 >(),
        (BinaryOp::LargerThan, NumberType::U16) => *result.cast::<bool>() = *a.cast::<u16>() > *b.cast::<u16>(),
        (BinaryOp::LargerThan, NumberType::U32) => *result.cast::<bool>() = *a.cast::<u32>() > *b.cast::<u32>(),
        (BinaryOp::LargerThan, NumberType::U64) => *result.cast::<bool>() = *a.cast::<u64>() > *b.cast::<u64>(),
        (BinaryOp::LargerThan, NumberType::I8)  => *result.cast::<bool>() = *a.cast::<i8 >() > *b.cast::<i8 >(),
        (BinaryOp::LargerThan, NumberType::I16) => *result.cast::<bool>() = *a.cast::<i16>() > *b.cast::<i16>(),
        (BinaryOp::LargerThan, NumberType::I32) => *result.cast::<bool>() = *a.cast::<i32>() > *b.cast::<i32>(),
        (BinaryOp::LargerThan, NumberType::I64) => *result.cast::<bool>() = *a.cast::<i64>() > *b.cast::<i64>(),
        (BinaryOp::LargerThan, NumberType::F32) => *result.cast::<bool>() = *a.cast::<f32>() > *b.cast::<f32>(),
        (BinaryOp::LargerThan, NumberType::F64) => *result.cast::<bool>() = *a.cast::<f64>() > *b.cast::<f64>(),

        (BinaryOp::LargerThanEquals, NumberType::U8)  => *result.cast::<bool>() = *a.cast::<u8 >() >= *b.cast::<u8 >(),
        (BinaryOp::LargerThanEquals, NumberType::U16) => *result.cast::<bool>() = *a.cast::<u16>() >= *b.cast::<u16>(),
        (BinaryOp::LargerThanEquals, NumberType::U32) => *result.cast::<bool>() = *a.cast::<u32>() >= *b.cast::<u32>(),
        (BinaryOp::LargerThanEquals, NumberType::U64) => *result.cast::<bool>() = *a.cast::<u64>() >= *b.cast::<u64>(),
        (BinaryOp::LargerThanEquals, NumberType::I8)  => *result.cast::<bool>() = *a.cast::<i8 >() >= *b.cast::<i8 >(),
        (BinaryOp::LargerThanEquals, NumberType::I16) => *result.cast::<bool>() = *a.cast::<i16>() >= *b.cast::<i16>(),
        (BinaryOp::LargerThanEquals, NumberType::I32) => *result.cast::<bool>() = *a.cast::<i32>() >= *b.cast::<i32>(),
        (BinaryOp::LargerThanEquals, NumberType::I64) => *result.cast::<bool>() = *a.cast::<i64>() >= *b.cast::<i64>(),
        (BinaryOp::LargerThanEquals, NumberType::F32) => *result.cast::<bool>() = *a.cast::<f32>() >= *b.cast::<f32>(),
        (BinaryOp::LargerThanEquals, NumberType::F64) => *result.cast::<bool>() = *a.cast::<f64>() >= *b.cast::<f64>(),

        (BinaryOp::And, NumberType::U8)  => *result.cast::<bool>() = (*a.cast::<u8>() > 0) & (*b.cast::<u8>() > 0),
        (BinaryOp::Or,  NumberType::U8)  => *result.cast::<bool>() = (*a.cast::<u8>() > 0) | (*b.cast::<u8>() > 0),


        _ => unreachable!(),
    }
}

/// Returns a u64 from some number of bytes.
fn u64_from_bytes(from: &[u8]) -> u64 {
    assert!(from.len() <= 8);
    let mut bytes = [0_u8; 8];
    bytes[..from.len()].copy_from_slice(from);
    u64::from_le_bytes(bytes)
}
