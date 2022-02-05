use crate::ir::{Instr, Routine, UserDefinedRoutine, PrimitiveType, StackValue, TypedLayout};
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::constant::ConstantRef;
use crate::program::{BuiltinFunction, Program, FunctionId};
use crate::types::BufferRepr;
use crate::type_infer::{TypeSystem, ValueId as TypeId, AstVariantId};
use crate::typer::AdditionalInfo;

mod stack;

pub use stack::{Stack, StackFrame, StackValueRef, StackValueMut};

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
        true,
    );
    let mut stack = Stack::new(2048);
    let result = interp(program, &mut stack, &routine, call_stack)?;
    Ok(program.insert_buffer(&types.value_to_compiler_type(TypeId::Node(variant_id, node)), result.as_ptr()))
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

        match *instr {
            Instr::LabelDefinition(_) => {}
            Instr::DebugLocation { .. } => {}
            Instr::JumpIfZero { condition, to } => {
                if unsafe { stack.get(condition).read::<u8>() } == 0 {
                    instr_pointer = routine.label_locations[to.0];
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
            }
            Instr::TargetBlock { target, to } => {
                if (target & crate::typer::TARGET_COMPILER) == 0 {
                    instr_pointer = routine.label_locations[to.0];
                }
            }
            Instr::CallImm {
                to,
                function_id,
                ref args,
                loc,
            } => {
                call_stack.push(loc);
                interp_function_call(program, stack, function_id, to, args, call_stack)?;
                call_stack.pop();
            }
            Instr::Call {
                to,
                pointer,
                ref args,
                loc,
            } => {
                call_stack.push(loc);
                interp_function_call(program, stack, unsafe { stack.get(pointer).read() }, to, args, call_stack)?;
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
            Instr::IndirectMove { to_ptr, from, offset, size } => {
                let to_ptr = unsafe { stack.get_mut(to_ptr).read::<*mut u8>() };
                let from_ptr = stack.get(from).as_ptr();
                unsafe {
                    std::ptr::copy(from_ptr, to_ptr.add(offset), size);
                }
            }
            Instr::Dereference { to, from_ptr, offset, size } => {
                let ptr = unsafe { stack.get(from_ptr).read::<*const u8>() };

                let to_ptr = stack.get_mut(to).as_mut_ptr();
                unsafe {
                    std::ptr::copy(ptr.add(offset), to_ptr, size);
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

        instr_pointer += 1;
    }

    // println!("\tRET");

    Ok(())
}

fn interp_function_call(
    program: &Program,
    stack: &mut StackFrame<'_>,
    function_id: FunctionId,
    to: (StackValue, TypedLayout),
    args: &[(StackValue, TypedLayout)],
    call_stack: &mut Vec<Location>,
) -> Result<(), Box<[Location]>> {
    let calling = program
        .get_routine(function_id)
        .expect("Invalid function pointer. There are two reasons this could happen; you bit_casted some number into a function pointer, or there is a bug in the compilers dependency system.");
    
    match &*calling {
        Routine::Extern(_) => {
            return Err(std::mem::take(call_stack).into_boxed_slice());
        }
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
            for (&(old, field_layout), new) in args.iter().zip(&calling.stack.values) {
                if field_layout.size() > 0 {
                    unsafe {
                        std::ptr::copy_nonoverlapping(
                            old_stack.get(old).as_ptr(),
                            new_stack.get_mut(new.value()).as_mut_ptr(),
                            field_layout.size(),
                        );
                    }
                }
            }

            interp_internal(program, &mut new_stack, calling, call_stack)?;

            if to.1.size() > 0 {
                unsafe {
                    std::ptr::copy_nonoverlapping(
                        new_stack.get(calling.result).as_ptr(),
                        old_stack.get_mut(to.0).as_mut_ptr(),
                        to.1.size(),
                    );
                }
            }
        }
    }

    Ok(())
}

pub unsafe fn run_unary_op(op: UnaryOp, result: *mut u8, a: *const u8, number: PrimitiveType) {
    match (op, number) {
        (UnaryOp::Not, PrimitiveType::Bool)  => *result.cast::<bool>() = !(*a.cast::<u8>() > 0),
        (UnaryOp::Not, PrimitiveType::U8)  => *result.cast::<u8 >() = !*a.cast::<u8 >(),
        (UnaryOp::Not, PrimitiveType::U16) => *result.cast::<u16>() = !*a.cast::<u16>(),
        (UnaryOp::Not, PrimitiveType::U32) => *result.cast::<u32>() = !*a.cast::<u32>(),
        (UnaryOp::Not, PrimitiveType::U64) => *result.cast::<u64>() = !*a.cast::<u64>(),
        (UnaryOp::Not, PrimitiveType::I8)  => *result.cast::<i8 >() = !*a.cast::<i8 >(),
        (UnaryOp::Not, PrimitiveType::I16) => *result.cast::<i16>() = !*a.cast::<i16>(),
        (UnaryOp::Not, PrimitiveType::I32) => *result.cast::<i32>() = !*a.cast::<i32>(),
        (UnaryOp::Not, PrimitiveType::I64) => *result.cast::<i64>() = !*a.cast::<i64>(),

        (UnaryOp::Negate, PrimitiveType::I8)  => *result.cast::<i8 >() = -*a.cast::<i8 >(),
        (UnaryOp::Negate, PrimitiveType::I16) => *result.cast::<i16>() = -*a.cast::<i16>(),
        (UnaryOp::Negate, PrimitiveType::I32) => *result.cast::<i32>() = -*a.cast::<i32>(),
        (UnaryOp::Negate, PrimitiveType::I64) => *result.cast::<i64>() = -*a.cast::<i64>(),
        (UnaryOp::Negate, PrimitiveType::F32) => *result.cast::<f32>() = -*a.cast::<f32>(),
        (UnaryOp::Negate, PrimitiveType::F64) => *result.cast::<f64>() = -*a.cast::<f64>(),

        _ => unreachable!(),
    }
}

pub unsafe fn convert_num(to: *mut u8, from: *const u8, to_num: PrimitiveType, from_num: PrimitiveType) {
    let middle = match from_num {
        PrimitiveType::Bool => *from.cast::<u8>() as i128,
        PrimitiveType::U8  => *from.cast::<u8>() as i128,
        PrimitiveType::U16 => *from.cast::<u16>() as i128,
        PrimitiveType::U32 => *from.cast::<u32>() as i128,
        PrimitiveType::U64 => *from.cast::<u64>() as i128,
        PrimitiveType::I8  => *from.cast::<i8 >() as i128,
        PrimitiveType::I16 => *from.cast::<i16>() as i128,
        PrimitiveType::I32 => *from.cast::<i32>() as i128,
        PrimitiveType::I64 => *from.cast::<i64>() as i128,
        PrimitiveType::F32 => *from.cast::<f32>() as i128,
        PrimitiveType::F64 => *from.cast::<f64>() as i128,
    };

    match to_num {
        PrimitiveType::Bool => *to.cast::<bool>() = middle > 0,
        PrimitiveType::U8  => *to.cast::<u8 >() = middle as _,
        PrimitiveType::U16 => *to.cast::<u16>() = middle as _,
        PrimitiveType::U32 => *to.cast::<u32>() = middle as _,
        PrimitiveType::U64 => *to.cast::<u64>() = middle as _,
        PrimitiveType::I8  => *to.cast::<i8 >() = middle as _,
        PrimitiveType::I16 => *to.cast::<i16>() = middle as _,
        PrimitiveType::I32 => *to.cast::<i32>() = middle as _,
        PrimitiveType::I64 => *to.cast::<i64>() = middle as _,
        PrimitiveType::F32 => *to.cast::<f32>() = middle as _,
        PrimitiveType::F64 => *to.cast::<f64>() = middle as _,
    }
}

pub unsafe fn run_binary_op(op: BinaryOp, result: *mut u8, a: *const u8, b: *const u8, number: PrimitiveType) {
    match (op, number) {
        // @TODO: These should give an assert failure if failing, and not fail in rust
        (BinaryOp::ShiftLeft, PrimitiveType::U8)  => *result.cast::<u8 >() = *a.cast::<u8 >() << *b.cast::<u8 >(),
        (BinaryOp::ShiftLeft, PrimitiveType::U16) => *result.cast::<u16>() = *a.cast::<u16>() << *b.cast::<u16>(),
        (BinaryOp::ShiftLeft, PrimitiveType::U32) => *result.cast::<u32>() = *a.cast::<u32>() << *b.cast::<u32>(),
        (BinaryOp::ShiftLeft, PrimitiveType::U64) => *result.cast::<u64>() = *a.cast::<u64>() << *b.cast::<u64>(),
        (BinaryOp::ShiftLeft, PrimitiveType::I8)  => *result.cast::<i8 >() = *a.cast::<i8 >() << *b.cast::<i8 >(),
        (BinaryOp::ShiftLeft, PrimitiveType::I16) => *result.cast::<i16>() = *a.cast::<i16>() << *b.cast::<i16>(),
        (BinaryOp::ShiftLeft, PrimitiveType::I32) => *result.cast::<i32>() = *a.cast::<i32>() << *b.cast::<i32>(),
        (BinaryOp::ShiftLeft, PrimitiveType::I64) => *result.cast::<i64>() = *a.cast::<i64>() << *b.cast::<i64>(),

        (BinaryOp::ShiftRight, PrimitiveType::U8)  => *result.cast::<u8 >() = *a.cast::<u8 >() >> *b.cast::<u8 >(),
        (BinaryOp::ShiftRight, PrimitiveType::U16) => *result.cast::<u16>() = *a.cast::<u16>() >> *b.cast::<u16>(),
        (BinaryOp::ShiftRight, PrimitiveType::U32) => *result.cast::<u32>() = *a.cast::<u32>() >> *b.cast::<u32>(),
        (BinaryOp::ShiftRight, PrimitiveType::U64) => *result.cast::<u64>() = *a.cast::<u64>() >> *b.cast::<u64>(),
        (BinaryOp::ShiftRight, PrimitiveType::I8)  => *result.cast::<i8 >() = *a.cast::<i8 >() >> *b.cast::<i8 >(),
        (BinaryOp::ShiftRight, PrimitiveType::I16) => *result.cast::<i16>() = *a.cast::<i16>() >> *b.cast::<i16>(),
        (BinaryOp::ShiftRight, PrimitiveType::I32) => *result.cast::<i32>() = *a.cast::<i32>() >> *b.cast::<i32>(),
        (BinaryOp::ShiftRight, PrimitiveType::I64) => *result.cast::<i64>() = *a.cast::<i64>() >> *b.cast::<i64>(),

        (BinaryOp::BitAnd, PrimitiveType::U8 | PrimitiveType::Bool)  => *result.cast::<u8 >() = *a.cast::<u8 >() & *b.cast::<u8 >(),
        (BinaryOp::BitAnd, PrimitiveType::U16) => *result.cast::<u16>() = *a.cast::<u16>() & *b.cast::<u16>(),
        (BinaryOp::BitAnd, PrimitiveType::U32) => *result.cast::<u32>() = *a.cast::<u32>() & *b.cast::<u32>(),
        (BinaryOp::BitAnd, PrimitiveType::U64) => *result.cast::<u64>() = *a.cast::<u64>() & *b.cast::<u64>(),
        (BinaryOp::BitAnd, PrimitiveType::I8)  => *result.cast::<i8 >() = *a.cast::<i8 >() & *b.cast::<i8 >(),
        (BinaryOp::BitAnd, PrimitiveType::I16) => *result.cast::<i16>() = *a.cast::<i16>() & *b.cast::<i16>(),
        (BinaryOp::BitAnd, PrimitiveType::I32) => *result.cast::<i32>() = *a.cast::<i32>() & *b.cast::<i32>(),
        (BinaryOp::BitAnd, PrimitiveType::I64) => *result.cast::<i64>() = *a.cast::<i64>() & *b.cast::<i64>(),

        (BinaryOp::BitOr, PrimitiveType::U8 | PrimitiveType::Bool)  => *result.cast::<u8 >() = *a.cast::<u8 >() | *b.cast::<u8 >(),
        (BinaryOp::BitOr, PrimitiveType::U16) => *result.cast::<u16>() = *a.cast::<u16>() | *b.cast::<u16>(),
        (BinaryOp::BitOr, PrimitiveType::U32) => *result.cast::<u32>() = *a.cast::<u32>() | *b.cast::<u32>(),
        (BinaryOp::BitOr, PrimitiveType::U64) => *result.cast::<u64>() = *a.cast::<u64>() | *b.cast::<u64>(),
        (BinaryOp::BitOr, PrimitiveType::I8)  => *result.cast::<i8 >() = *a.cast::<i8 >() | *b.cast::<i8 >(),
        (BinaryOp::BitOr, PrimitiveType::I16) => *result.cast::<i16>() = *a.cast::<i16>() | *b.cast::<i16>(),
        (BinaryOp::BitOr, PrimitiveType::I32) => *result.cast::<i32>() = *a.cast::<i32>() | *b.cast::<i32>(),
        (BinaryOp::BitOr, PrimitiveType::I64) => *result.cast::<i64>() = *a.cast::<i64>() | *b.cast::<i64>(),

        (BinaryOp::Add, PrimitiveType::U8)  => *result.cast::<u8 >() = (*a.cast::<u8 >()).wrapping_add(*b.cast::<u8 >()),
        (BinaryOp::Add, PrimitiveType::U16) => *result.cast::<u16>() = (*a.cast::<u16>()).wrapping_add(*b.cast::<u16>()),
        (BinaryOp::Add, PrimitiveType::U32) => *result.cast::<u32>() = (*a.cast::<u32>()).wrapping_add(*b.cast::<u32>()),
        (BinaryOp::Add, PrimitiveType::U64) => *result.cast::<u64>() = (*a.cast::<u64>()).wrapping_add(*b.cast::<u64>()),
        (BinaryOp::Add, PrimitiveType::I8)  => *result.cast::<i8 >() = (*a.cast::<i8 >()).wrapping_add(*b.cast::<i8 >()),
        (BinaryOp::Add, PrimitiveType::I16) => *result.cast::<i16>() = (*a.cast::<i16>()).wrapping_add(*b.cast::<i16>()),
        (BinaryOp::Add, PrimitiveType::I32) => *result.cast::<i32>() = (*a.cast::<i32>()).wrapping_add(*b.cast::<i32>()),
        (BinaryOp::Add, PrimitiveType::I64) => *result.cast::<i64>() = (*a.cast::<i64>()).wrapping_add(*b.cast::<i64>()),
        (BinaryOp::Add, PrimitiveType::F32) => *result.cast::<f32>() = *a.cast::<f32>() + *b.cast::<f32>(),
        (BinaryOp::Add, PrimitiveType::F64) => *result.cast::<f64>() = *a.cast::<f64>() + *b.cast::<f64>(),

        (BinaryOp::Sub, PrimitiveType::U8)  => *result.cast::<u8 >() = (*a.cast::<u8 >()).wrapping_sub(*b.cast::<u8 >()),
        (BinaryOp::Sub, PrimitiveType::U16) => *result.cast::<u16>() = (*a.cast::<u16>()).wrapping_sub(*b.cast::<u16>()),
        (BinaryOp::Sub, PrimitiveType::U32) => *result.cast::<u32>() = (*a.cast::<u32>()).wrapping_sub(*b.cast::<u32>()),
        (BinaryOp::Sub, PrimitiveType::U64) => *result.cast::<u64>() = (*a.cast::<u64>()).wrapping_sub(*b.cast::<u64>()),
        (BinaryOp::Sub, PrimitiveType::I8)  => *result.cast::<i8 >() = (*a.cast::<i8 >()).wrapping_sub(*b.cast::<i8 >()),
        (BinaryOp::Sub, PrimitiveType::I16) => *result.cast::<i16>() = (*a.cast::<i16>()).wrapping_sub(*b.cast::<i16>()),
        (BinaryOp::Sub, PrimitiveType::I32) => *result.cast::<i32>() = (*a.cast::<i32>()).wrapping_sub(*b.cast::<i32>()),
        (BinaryOp::Sub, PrimitiveType::I64) => *result.cast::<i64>() = (*a.cast::<i64>()).wrapping_sub(*b.cast::<i64>()),
        (BinaryOp::Sub, PrimitiveType::F32) => *result.cast::<f32>() = *a.cast::<f32>() - *b.cast::<f32>(),
        (BinaryOp::Sub, PrimitiveType::F64) => *result.cast::<f64>() = *a.cast::<f64>() - *b.cast::<f64>(),

        (BinaryOp::Mult, PrimitiveType::U8)  => *result.cast::<u8 >() = (*a.cast::<u8 >()).wrapping_mul(*b.cast::<u8 >()),
        (BinaryOp::Mult, PrimitiveType::U16) => *result.cast::<u16>() = (*a.cast::<u16>()).wrapping_mul(*b.cast::<u16>()),
        (BinaryOp::Mult, PrimitiveType::U32) => *result.cast::<u32>() = (*a.cast::<u32>()).wrapping_mul(*b.cast::<u32>()),
        (BinaryOp::Mult, PrimitiveType::U64) => *result.cast::<u64>() = (*a.cast::<u64>()).wrapping_mul(*b.cast::<u64>()),
        (BinaryOp::Mult, PrimitiveType::I8)  => *result.cast::<i8 >() = (*a.cast::<i8 >()).wrapping_mul(*b.cast::<i8 >()),
        (BinaryOp::Mult, PrimitiveType::I16) => *result.cast::<i16>() = (*a.cast::<i16>()).wrapping_mul(*b.cast::<i16>()),
        (BinaryOp::Mult, PrimitiveType::I32) => *result.cast::<i32>() = (*a.cast::<i32>()).wrapping_mul(*b.cast::<i32>()),
        (BinaryOp::Mult, PrimitiveType::I64) => *result.cast::<i64>() = (*a.cast::<i64>()).wrapping_mul(*b.cast::<i64>()),
        (BinaryOp::Mult, PrimitiveType::F32) => *result.cast::<f32>() = *a.cast::<f32>() * *b.cast::<f32>(),
        (BinaryOp::Mult, PrimitiveType::F64) => *result.cast::<f64>() = *a.cast::<f64>() * *b.cast::<f64>(),

        // TODO: Should these cause assert failures?
        (BinaryOp::Div, PrimitiveType::U8)  => *result.cast::<u8 >() = (*a.cast::<u8 >()).checked_div(*b.cast::<u8 >()).unwrap_or(0),
        (BinaryOp::Div, PrimitiveType::U16) => *result.cast::<u16>() = (*a.cast::<u16>()).checked_div(*b.cast::<u16>()).unwrap_or(0),
        (BinaryOp::Div, PrimitiveType::U32) => *result.cast::<u32>() = (*a.cast::<u32>()).checked_div(*b.cast::<u32>()).unwrap_or(0),
        (BinaryOp::Div, PrimitiveType::U64) => *result.cast::<u64>() = (*a.cast::<u64>()).checked_div(*b.cast::<u64>()).unwrap_or(0),
        (BinaryOp::Div, PrimitiveType::I8)  => *result.cast::<i8 >() = (*a.cast::<i8 >()).checked_div(*b.cast::<i8 >()).unwrap_or(0),
        (BinaryOp::Div, PrimitiveType::I16) => *result.cast::<i16>() = (*a.cast::<i16>()).checked_div(*b.cast::<i16>()).unwrap_or(0),
        (BinaryOp::Div, PrimitiveType::I32) => *result.cast::<i32>() = (*a.cast::<i32>()).checked_div(*b.cast::<i32>()).unwrap_or(0),
        (BinaryOp::Div, PrimitiveType::I64) => *result.cast::<i64>() = (*a.cast::<i64>()).checked_div(*b.cast::<i64>()).unwrap_or(0),
        (BinaryOp::Div, PrimitiveType::F32) => *result.cast::<f32>() = *a.cast::<f32>() / *b.cast::<f32>(),
        (BinaryOp::Div, PrimitiveType::F64) => *result.cast::<f64>() = *a.cast::<f64>() / *b.cast::<f64>(),

        (BinaryOp::Modulo, PrimitiveType::U8)  => *result.cast::<u8 >() = (*a.cast::<u8 >()).checked_rem(*b.cast::<u8 >()).unwrap_or(0),
        (BinaryOp::Modulo, PrimitiveType::U16) => *result.cast::<u16>() = (*a.cast::<u16>()).checked_rem(*b.cast::<u16>()).unwrap_or(0),
        (BinaryOp::Modulo, PrimitiveType::U32) => *result.cast::<u32>() = (*a.cast::<u32>()).checked_rem(*b.cast::<u32>()).unwrap_or(0),
        (BinaryOp::Modulo, PrimitiveType::U64) => *result.cast::<u64>() = (*a.cast::<u64>()).checked_rem(*b.cast::<u64>()).unwrap_or(0),
        (BinaryOp::Modulo, PrimitiveType::I8)  => *result.cast::<i8 >() = (*a.cast::<i8 >()).checked_rem(*b.cast::<i8 >()).unwrap_or(0),
        (BinaryOp::Modulo, PrimitiveType::I16) => *result.cast::<i16>() = (*a.cast::<i16>()).checked_rem(*b.cast::<i16>()).unwrap_or(0),
        (BinaryOp::Modulo, PrimitiveType::I32) => *result.cast::<i32>() = (*a.cast::<i32>()).checked_rem(*b.cast::<i32>()).unwrap_or(0),
        (BinaryOp::Modulo, PrimitiveType::I64) => *result.cast::<i64>() = (*a.cast::<i64>()).checked_rem(*b.cast::<i64>()).unwrap_or(0),
        (BinaryOp::Modulo, PrimitiveType::F32) => *result.cast::<f32>() = *a.cast::<f32>() / *b.cast::<f32>(),
        (BinaryOp::Modulo, PrimitiveType::F64) => *result.cast::<f64>() = *a.cast::<f64>() / *b.cast::<f64>(),

        (BinaryOp::Equals, PrimitiveType::U8 | PrimitiveType::Bool)  => *result.cast::<bool>() = *a.cast::<u8 >() == *b.cast::<u8 >(),
        (BinaryOp::Equals, PrimitiveType::U16) => *result.cast::<bool>() = *a.cast::<u16>() == *b.cast::<u16>(),
        (BinaryOp::Equals, PrimitiveType::U32) => *result.cast::<bool>() = *a.cast::<u32>() == *b.cast::<u32>(),
        (BinaryOp::Equals, PrimitiveType::U64) => *result.cast::<bool>() = *a.cast::<u64>() == *b.cast::<u64>(),
        (BinaryOp::Equals, PrimitiveType::I8)  => *result.cast::<bool>() = *a.cast::<i8 >() == *b.cast::<i8 >(),
        (BinaryOp::Equals, PrimitiveType::I16) => *result.cast::<bool>() = *a.cast::<i16>() == *b.cast::<i16>(),
        (BinaryOp::Equals, PrimitiveType::I32) => *result.cast::<bool>() = *a.cast::<i32>() == *b.cast::<i32>(),
        (BinaryOp::Equals, PrimitiveType::I64) => *result.cast::<bool>() = *a.cast::<i64>() == *b.cast::<i64>(),
        (BinaryOp::Equals, PrimitiveType::F32) => *result.cast::<bool>() = *a.cast::<f32>() == *b.cast::<f32>(),
        (BinaryOp::Equals, PrimitiveType::F64) => *result.cast::<bool>() = *a.cast::<f64>() == *b.cast::<f64>(),

        (BinaryOp::NotEquals, PrimitiveType::U8 | PrimitiveType::Bool)  => *result.cast::<bool>() = *a.cast::<u8 >() != *b.cast::<u8 >(),
        (BinaryOp::NotEquals, PrimitiveType::U16) => *result.cast::<bool>() = *a.cast::<u16>() != *b.cast::<u16>(),
        (BinaryOp::NotEquals, PrimitiveType::U32) => *result.cast::<bool>() = *a.cast::<u32>() != *b.cast::<u32>(),
        (BinaryOp::NotEquals, PrimitiveType::U64) => *result.cast::<bool>() = *a.cast::<u64>() != *b.cast::<u64>(),
        (BinaryOp::NotEquals, PrimitiveType::I8)  => *result.cast::<bool>() = *a.cast::<i8 >() != *b.cast::<i8 >(),
        (BinaryOp::NotEquals, PrimitiveType::I16) => *result.cast::<bool>() = *a.cast::<i16>() != *b.cast::<i16>(),
        (BinaryOp::NotEquals, PrimitiveType::I32) => *result.cast::<bool>() = *a.cast::<i32>() != *b.cast::<i32>(),
        (BinaryOp::NotEquals, PrimitiveType::I64) => *result.cast::<bool>() = *a.cast::<i64>() != *b.cast::<i64>(),
        (BinaryOp::NotEquals, PrimitiveType::F32) => *result.cast::<bool>() = *a.cast::<f32>() != *b.cast::<f32>(),
        (BinaryOp::NotEquals, PrimitiveType::F64) => *result.cast::<bool>() = *a.cast::<f64>() != *b.cast::<f64>(),

        (BinaryOp::LessThan, PrimitiveType::U8)  => *result.cast::<bool>() = *a.cast::<u8 >() < *b.cast::<u8 >(),
        (BinaryOp::LessThan, PrimitiveType::U16) => *result.cast::<bool>() = *a.cast::<u16>() < *b.cast::<u16>(),
        (BinaryOp::LessThan, PrimitiveType::U32) => *result.cast::<bool>() = *a.cast::<u32>() < *b.cast::<u32>(),
        (BinaryOp::LessThan, PrimitiveType::U64) => *result.cast::<bool>() = *a.cast::<u64>() < *b.cast::<u64>(),
        (BinaryOp::LessThan, PrimitiveType::I8)  => *result.cast::<bool>() = *a.cast::<i8 >() < *b.cast::<i8 >(),
        (BinaryOp::LessThan, PrimitiveType::I16) => *result.cast::<bool>() = *a.cast::<i16>() < *b.cast::<i16>(),
        (BinaryOp::LessThan, PrimitiveType::I32) => *result.cast::<bool>() = *a.cast::<i32>() < *b.cast::<i32>(),
        (BinaryOp::LessThan, PrimitiveType::I64) => *result.cast::<bool>() = *a.cast::<i64>() < *b.cast::<i64>(),
        (BinaryOp::LessThan, PrimitiveType::F32) => *result.cast::<bool>() = *a.cast::<f32>() < *b.cast::<f32>(),
        (BinaryOp::LessThan, PrimitiveType::F64) => *result.cast::<bool>() = *a.cast::<f64>() < *b.cast::<f64>(),

        (BinaryOp::LessThanEquals, PrimitiveType::U8)  => *result.cast::<bool>() = *a.cast::<u8 >() <= *b.cast::<u8 >(),
        (BinaryOp::LessThanEquals, PrimitiveType::U16) => *result.cast::<bool>() = *a.cast::<u16>() <= *b.cast::<u16>(),
        (BinaryOp::LessThanEquals, PrimitiveType::U32) => *result.cast::<bool>() = *a.cast::<u32>() <= *b.cast::<u32>(),
        (BinaryOp::LessThanEquals, PrimitiveType::U64) => *result.cast::<bool>() = *a.cast::<u64>() <= *b.cast::<u64>(),
        (BinaryOp::LessThanEquals, PrimitiveType::I8)  => *result.cast::<bool>() = *a.cast::<i8 >() <= *b.cast::<i8 >(),
        (BinaryOp::LessThanEquals, PrimitiveType::I16) => *result.cast::<bool>() = *a.cast::<i16>() <= *b.cast::<i16>(),
        (BinaryOp::LessThanEquals, PrimitiveType::I32) => *result.cast::<bool>() = *a.cast::<i32>() <= *b.cast::<i32>(),
        (BinaryOp::LessThanEquals, PrimitiveType::I64) => *result.cast::<bool>() = *a.cast::<i64>() <= *b.cast::<i64>(),
        (BinaryOp::LessThanEquals, PrimitiveType::F32) => *result.cast::<bool>() = *a.cast::<f32>() <= *b.cast::<f32>(),
        (BinaryOp::LessThanEquals, PrimitiveType::F64) => *result.cast::<bool>() = *a.cast::<f64>() <= *b.cast::<f64>(),

        (BinaryOp::LargerThan, PrimitiveType::U8)  => *result.cast::<bool>() = *a.cast::<u8 >() > *b.cast::<u8 >(),
        (BinaryOp::LargerThan, PrimitiveType::U16) => *result.cast::<bool>() = *a.cast::<u16>() > *b.cast::<u16>(),
        (BinaryOp::LargerThan, PrimitiveType::U32) => *result.cast::<bool>() = *a.cast::<u32>() > *b.cast::<u32>(),
        (BinaryOp::LargerThan, PrimitiveType::U64) => *result.cast::<bool>() = *a.cast::<u64>() > *b.cast::<u64>(),
        (BinaryOp::LargerThan, PrimitiveType::I8)  => *result.cast::<bool>() = *a.cast::<i8 >() > *b.cast::<i8 >(),
        (BinaryOp::LargerThan, PrimitiveType::I16) => *result.cast::<bool>() = *a.cast::<i16>() > *b.cast::<i16>(),
        (BinaryOp::LargerThan, PrimitiveType::I32) => *result.cast::<bool>() = *a.cast::<i32>() > *b.cast::<i32>(),
        (BinaryOp::LargerThan, PrimitiveType::I64) => *result.cast::<bool>() = *a.cast::<i64>() > *b.cast::<i64>(),
        (BinaryOp::LargerThan, PrimitiveType::F32) => *result.cast::<bool>() = *a.cast::<f32>() > *b.cast::<f32>(),
        (BinaryOp::LargerThan, PrimitiveType::F64) => *result.cast::<bool>() = *a.cast::<f64>() > *b.cast::<f64>(),

        (BinaryOp::LargerThanEquals, PrimitiveType::U8)  => *result.cast::<bool>() = *a.cast::<u8 >() >= *b.cast::<u8 >(),
        (BinaryOp::LargerThanEquals, PrimitiveType::U16) => *result.cast::<bool>() = *a.cast::<u16>() >= *b.cast::<u16>(),
        (BinaryOp::LargerThanEquals, PrimitiveType::U32) => *result.cast::<bool>() = *a.cast::<u32>() >= *b.cast::<u32>(),
        (BinaryOp::LargerThanEquals, PrimitiveType::U64) => *result.cast::<bool>() = *a.cast::<u64>() >= *b.cast::<u64>(),
        (BinaryOp::LargerThanEquals, PrimitiveType::I8)  => *result.cast::<bool>() = *a.cast::<i8 >() >= *b.cast::<i8 >(),
        (BinaryOp::LargerThanEquals, PrimitiveType::I16) => *result.cast::<bool>() = *a.cast::<i16>() >= *b.cast::<i16>(),
        (BinaryOp::LargerThanEquals, PrimitiveType::I32) => *result.cast::<bool>() = *a.cast::<i32>() >= *b.cast::<i32>(),
        (BinaryOp::LargerThanEquals, PrimitiveType::I64) => *result.cast::<bool>() = *a.cast::<i64>() >= *b.cast::<i64>(),
        (BinaryOp::LargerThanEquals, PrimitiveType::F32) => *result.cast::<bool>() = *a.cast::<f32>() >= *b.cast::<f32>(),
        (BinaryOp::LargerThanEquals, PrimitiveType::F64) => *result.cast::<bool>() = *a.cast::<f64>() >= *b.cast::<f64>(),

        (BinaryOp::And, PrimitiveType::U8 | PrimitiveType::Bool)  => *result.cast::<bool>() = (*a.cast::<u8>() > 0) & (*b.cast::<u8>() > 0),
        (BinaryOp::Or,  PrimitiveType::U8 | PrimitiveType::Bool)  => *result.cast::<bool>() = (*a.cast::<u8>() > 0) | (*b.cast::<u8>() > 0),


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
