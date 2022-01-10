use crate::ir::{Instr, UserDefinedRoutine, Routine, LabelId, PrimitiveType, Value};
use crate::layout::{align_to, StructLayout, Layout};
use crate::program::{Program, FunctionId};
use crate::types::PointerInType;
use crate::types::Type;
use crate::operators::{BinaryOp, UnaryOp};
use std::path::Path;
use std::fmt::{self, Write};
use super::{Formatter, function_symbol, global_symbol};
use std::cmp::{Ord, Ordering};

#[derive(Default)]
pub struct Emitter {
    extern_defs: String,
    p_data: String,
    x_data: String,
    text: String,
}

impl Emitter {
    pub fn emit_routine(
        &mut self, 
        program: &Program,
        function_id: FunctionId,
        routine: &Routine,
        _args: &[Type],
        _returns: Type,
    ) {
        match routine {
            Routine::UserDefined(routine) => {
                emit_routine(&mut self.text, &mut self.extern_defs, &mut self.p_data, &mut self.x_data, program, function_id, routine).unwrap();
            }
            Routine::Extern(symbol_name) => {
                writeln!(&mut self.extern_defs, "extern {}", symbol_name).unwrap();
            }
            _ => {}
        }
    }
}

pub fn emit(program: &Program, file_path: &Path, emitters: Vec<Emitter>) {
    let mut out = String::new();

    for emitter in &emitters {
        write!(&mut out, "{}", emitter.extern_defs).unwrap();
    }

    writeln!(&mut out, "\nsection .data").unwrap();
    emit_constants(&mut out, program);

    writeln!(&mut out, "\nsection .text").unwrap();

    for emitter in &emitters {
        write!(&mut out, "{}", emitter.text).unwrap();
    }

    writeln!(&mut out, "\nsection .pdata rdata align=4").unwrap();

    for emitter in &emitters {
        write!(&mut out, "{}", emitter.p_data).unwrap();
    }

    writeln!(&mut out, "\nsection .xdata rdata align=8").unwrap();

    for emitter in &emitters {
        write!(&mut out, "{}", emitter.x_data).unwrap();
    }

    if let Err(_) = std::fs::write(file_path, &out) {
        eprintln!("Failed to write x64 assembly to {}", file_path.display());
    }
}

pub fn emit_constants(out: &mut String, program: &Program) {
    let constant_data = program.constant_data();
    for constant in constant_data.iter() {
        let ptr = constant.ptr.as_ptr();

        write!(out, "\t{}: dq ", global_symbol(ptr as usize)).unwrap();

        let mut pointers = constant.type_.pointers().iter().peekable();
        for i in (0..constant.type_.size()).step_by(8) {
            match pointers.peek() {
                Some(&(offset, pointer_kind)) if *offset == i => {
                    let ptr_num = unsafe { *ptr.add(i).cast::<usize>() };
                    if let PointerInType::Function { .. } = pointer_kind {
                        let function_id = ptr_num.into();
                        let routine = program.get_routine(function_id).unwrap();

                        match &*routine {
                            Routine::Extern(symbol_name) => {
                                write!(out, "{}", symbol_name).unwrap();
                            }
                            _ => {
                                write!(out, "{}", function_symbol(ptr_num.into())).unwrap();
                            }
                        }
                    } else if ptr_num == 0 {
                        out.push('0');
                    } else {
                        write!(out, "{}", global_symbol(ptr_num)).unwrap();
                    }
                    pointers.next();
                }
                _ => {
                    write!(out, "{}", unsafe { *ptr.add(i).cast::<u64>() }).unwrap();
                }
            }

            out.push_str(", ");
        }
        writeln!(out).unwrap();
    }
}

fn name_of_size(size: usize) -> &'static str {
    match size {
        1 => "BYTE",
        2 => "WORD",
        4 => "DWORD",
        8 => "QWORD",
        _ => unreachable!("This size has no name"),
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
enum Register {
    Rax,
    Rbx,
    Rcx,
    Rdx,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

impl Register {
    fn name(self, size: usize) -> &'static str {
        match (self, size) {
            (Self::Rax, 1) =>  "al",
            (Self::Rax, 2) =>  "ax",
            (Self::Rax, 4) => "eax",
            (Self::Rax, 8) => "rax",
            (Self::Rbx, 1) =>  "bl",
            (Self::Rbx, 2) =>  "bx",
            (Self::Rbx, 4) => "ebx",
            (Self::Rbx, 8) => "rbx",
            (Self::Rcx, 1) =>  "cl",
            (Self::Rcx, 2) =>  "cx",
            (Self::Rcx, 4) => "ecx",
            (Self::Rcx, 8) => "rcx",
            (Self::Rdx, 1) =>  "dl",
            (Self::Rdx, 2) =>  "dx",
            (Self::Rdx, 4) => "edx",
            (Self::Rdx, 8) => "rdx",
            (Self::R8, 1) => "r8b",
            (Self::R8, 2) => "r8w",
            (Self::R8, 4) => "r8d",
            (Self::R8, 8) => "r8",
            (Self::R9, 1) => "r9b",
            (Self::R9, 2) => "r9w",
            (Self::R9, 4) => "r9d",
            (Self::R9, 8) => "r9",
            (Self::R10, 1) => "r10b",
            (Self::R10, 2) => "r10w",
            (Self::R10, 4) => "r10d",
            (Self::R10, 8) => "r10",
            (Self::R11, 1) => "r11b",
            (Self::R11, 2) => "r11w",
            (Self::R11, 4) => "r11d",
            (Self::R11, 8) => "r11",
            (reg, size) => unreachable!("Invalid combination of register and size, {:?}, size {}", reg, size),
        }
    }
}

#[derive(Clone, Copy)]
struct SizeSplit {
    offset: usize,
    size: usize,
}

fn label_name(function: FunctionId, label: LabelId) -> impl fmt::Display {
    Formatter(move |f| write!(f, "label_{}_{}", usize::from(function), label.0))
}

fn split_into_powers_of_two(mut value: usize) -> impl Iterator<Item = SizeSplit> {
    let mut offset = 0;
    std::iter::from_fn(move || {
        if value == 0 {
            None
        } else if value <= 8 && value.is_power_of_two() {
            let size = SizeSplit {
                offset,
                size: value,
            };
            value = 0;
            Some(size)
        } else {
            let current = if value >= 8 {
                8
            } else {
                value.next_power_of_two() / 2
            };

            let size = SizeSplit {
                offset,
                size: current,
            };
            value -= current;
            offset += current;
            Some(size)
        }
    })
}

struct Stack {
    offset: usize,
    stack_size: usize,
}

impl Stack {
    fn value_with_offset(&self, value: &Value, offset: usize) -> impl fmt::Display {
        let result = self.offset - self.stack_size + value.0 + offset;
        Formatter(move |f| write!(f, "[rsp+{}]", result))
    }

    fn value(&self, value: &Value) -> impl fmt::Display {
        let result = self.offset - self.stack_size + value.0;
        Formatter(move |f| write!(f, "[rsp+{}]", result))
    }
}

fn emit_routine(
    out: &mut String,
    extern_defs: &mut String,
    p_data: &mut String,
    x_data: &mut String,
    program: &Program,
    function_id: FunctionId,
    routine: &UserDefinedRoutine,
) -> fmt::Result {
    let is_debugging = program.arguments.debug;

    if is_debugging {
        let loc = routine.loc;
        let file_str = loc.file.as_str().strip_prefix("\\\\?\\").unwrap_or(loc.file.as_str());
        writeln!(out, "# {}+0 {:?}", loc.line, file_str)?;

        writeln!(extern_defs, "# {}+0 {:?}", loc.line, file_str)?;
        writeln!(p_data, "# {}+0 {:?}", loc.line, file_str)?;
        writeln!(x_data, "# {}+0 {:?}", loc.line, file_str)?;
    }

    writeln!(extern_defs, "global {}", function_symbol(function_id)).unwrap();

    writeln!(out, "; {}", routine.name)?;
    writeln!(out, "{}:", function_symbol(function_id))?;

    // @Incomplete: We want to later on track the max alignment used in the stack, and manually align it if it's
    // greater than 16 bytes.
    let stack_size = routine.stack.max;

    let mut stack = Stack {
        offset: align_to(stack_size + 8, 16) - 8,
        stack_size: stack_size,
    };

    let mut function_args_offset = 0;
    for instr in &routine.instr {
        if let Instr::Call { to: (_, to_layout), pointer: _, ref args, loc: _ } = instr {
            let mut args_layouts = StructLayout::new_with_align(0, 16);
            let mut scratch_region_layout = StructLayout::new_with_align(0, 16);
            let mut num_args = 0;
            if to_layout.size() > 8 {
                // The return value is passed as a pointer, so we need 8 extra bytes to the return stack.
                args_layouts.next(Layout::PTR);
                num_args += 1;
            }
            for &(_, arg_layout) in args {
                if arg_layout.size() > 8 || !arg_layout.size().is_power_of_two() {
                    args_layouts.next(Layout::PTR);
                    scratch_region_layout.next(arg_layout.layout);
                } else {
                    if num_args < 4 {
                        args_layouts.next(Layout::U64);
                    } else {
                        args_layouts.next(arg_layout.layout);
                    }
                }
            }
            for &(_, arg_layout) in args {
                if arg_layout.size() > 8 || !arg_layout.size().is_power_of_two() {
                    scratch_region_layout.next(arg_layout.layout);
                }
            }
            args_layouts.position = args_layouts.position.max(32);
            function_args_offset = function_args_offset.max(args_layouts.size() + scratch_region_layout.size());
        }
    }
    stack.offset += function_args_offset;

    writeln!(out, "\tsub rsp, {}", stack.offset)?;

    writeln!(out, "{}_prolog_end:", function_symbol(function_id))?;

    // @Incomplete: Copy over the arguments from where they were passed
    // Do this to ignore the return function pointer that's also on the stack at this point.
    let mut to_stack = StructLayout::new(0);
    let mut arg_pos = StructLayout::new_with_align(stack.offset + 8, 16);
    let mut args_read = 0;

    if routine.result_layout.size() > 0 && (routine.result_layout.size() > 8 || !routine.result_layout.size().is_power_of_two()) {
        let stack_pos = arg_pos.next(Layout::PTR);
        writeln!(
            out,
            "\tmov [rsp+{}], rcx",
            stack_pos,
        )?;
        args_read += 1;
    }

    for &(_, arg_layout) in &routine.args {
        if arg_layout.size() == 0 { continue; }

        let reg = [Register::Rcx, Register::Rdx, Register::R8, Register::R9].get(args_read).copied();

        if arg_layout.size() > 8 || !arg_layout.size().is_power_of_two() {
            let reg = if let Some(reg) = reg {
                arg_pos.next(Layout::U64);
                reg
            } else {
                let stack_pos = arg_pos.next(Layout::PTR);
                writeln!(
                    out,
                    "\tlea rcx, [rsp+{}]",
                    stack_pos,
                )?;
                Register::Rcx
            };

            let write_to = to_stack.next(arg_layout.layout);
            for split in split_into_powers_of_two(arg_layout.size()) {
                let reg_name = Register::Rax.name(split.size);
                writeln!(out, "\tmov {}, {} [{}+{}]", reg_name, name_of_size(split.size), reg.name(8), split.offset)?;
                writeln!(out, "\tmov {} [rsp+{}], {}", name_of_size(split.size), write_to + split.offset, reg_name)?;
            }
        } else {
            let write_to = to_stack.next(arg_layout.layout);

            if let Some(reg) = reg {
                arg_pos.next(Layout::U64);
                writeln!(
                    out,
                    "\tmov [rsp+{}], {}",
                    write_to,
                    reg.name(arg_layout.size()),
                )?;
            } else {
                let stack_pos = arg_pos.next(arg_layout.layout);
                let reg_name = Register::Rcx.name(arg_layout.size());
                writeln!(
                    out,
                    "\tmov {}, [rsp+{}]",
                    reg_name,
                    stack_pos,
                )?;
                writeln!(
                    out,
                    "\tmov [rsp+{}], {}",
                    write_to,
                    reg_name,
                )?;
            }
        }

        args_read += 1;
    }

    for instr in &routine.instr {
        match *instr {
            Instr::DebugLocation(loc) => {
                if is_debugging {
                    writeln!(out, "# {}+0 {:?}", loc.line, loc.file.as_str().strip_prefix("\\\\?\\").unwrap_or(loc.file.as_str())).unwrap();
                }
            }
            Instr::Call { to: (to, to_layout), pointer, ref args, loc: _ } => {
                // @Incomplete: We want to look at which calling convention we're using here too,
                // for now we just assume the standard x64 convention

                let mut args_layouts = StructLayout::new_with_align(0, 16);
                let mut scratch_region_layout = StructLayout::new_with_align(0, 16);
                let mut num_args = 0;

                if to_layout.size() > 8 {
                    // The return value is passed as a pointer, so we need 8 extra bytes to the return stack.
                    args_layouts.next(Layout::PTR);
                    num_args += 1;
                }

                for &(_, arg_layout) in args {
                    if arg_layout.size() > 8 || !arg_layout.size().is_power_of_two() {
                        // Pass as pointer instead
                        args_layouts.next(Layout::PTR);
                        // We're passing as value, so we can't let the caller modify us even though we're passing a pointer.
                        // Therefore, we also allocate space for a temporary value of the argument
                        scratch_region_layout.next(arg_layout.layout);
                    } else {
                        if num_args < 4 {
                            args_layouts.next(Layout::U64);
                        } else {
                            // @Correctness: I'm not sure this is correct, but it seems to be what you're supposed to do?
                            args_layouts.next(arg_layout.layout);
                        }
                    }

                    num_args += 1;
                }

                args_layouts.position = args_layouts.position.max(32);

                {
                    let mut scratch_region_layout = StructLayout::new_with_align(args_layouts.size(), 16);
                    for &(arg, arg_layout) in args {
                        if arg_layout.size() > 8 || !arg_layout.size().is_power_of_two() {
                            let from = arg;
                            let to = scratch_region_layout.next(arg_layout.layout);
                            for split in split_into_powers_of_two(arg_layout.size()) {
                                let reg_name = Register::Rax.name(split.size);
                                writeln!(out, "\tmov {}, {} {}", reg_name, name_of_size(split.size), stack.value(&from))?;
                                writeln!(out, "\tmov {} [rsp+{}], {}", name_of_size(split.size), to, reg_name)?;
                            }
                        }
                    }
                }

                let mut arguments_passed = 0;
                let mut arg_pos = StructLayout::new_with_align(0, 16);
                let mut scratch_region_pos = StructLayout::new_with_align(args_layouts.size(), 16);

                // @TODO: Check if it's a float too.
                // @TODO: This doesn't check if it has a constructor or not. We don't have constructors,
                // but if we call into c++, this might matter... :(
                if to_layout.size() > 0 && (to_layout.size() > 8 || !to_layout.size().is_power_of_two()) {
                    // We need to pass a pointer to the return value as the first argument
                    writeln!(
                        out,
                        "\nlea {}, {}",
                        Register::Rcx.name(8),
                        stack.value(&to)
                    )?;

                    arguments_passed += 1;
                    arg_pos.next(Layout::PTR);
                }

                for &(arg, arg_layout) in args.iter() {
                    if arg_layout.size() == 0 { continue; }

                    let reg = [Register::Rcx, Register::Rdx, Register::R8, Register::R9].get(arguments_passed).copied();
                    if arg_layout.size() > 8 || !arg_layout.size().is_power_of_two() {
                        let from_pos = scratch_region_pos.next(arg_layout.layout);

                        if let Some(reg) = reg {
                            arg_pos.next(Layout::U64);
                            writeln!(
                                out,
                                "\tlea {}, [rsp+{}]",
                                reg.name(8),
                                from_pos,
                            )?;
                        } else {
                            let arg_stackpos = arg_pos.next(Layout::PTR);
                            // @Correctness: `rbx` is non-volatile, we shouldn't modify it.
                            writeln!(
                                out,
                                "\tlea rbx, [rsp+{}]",
                                from_pos,
                            )?;
                            writeln!(
                                out,
                                "\tmov [rsp+{}], rbx",
                                arg_stackpos,
                            )?;
                        }
                    } else {
                        if let Some(reg) = reg {
                            // Registers always seem to take up 64 bits of stack for some reason?
                            arg_pos.next(Layout::U64);

                            writeln!(
                                out,
                                "\tmov {}, {}",
                                reg.name(arg_layout.size()),
                                stack.value(&arg),
                            )?;
                        } else {
                            let arg_stackpos = arg_pos.next(arg_layout.layout);

                            let reg_name = Register::Rcx.name(arg_layout.size());
                            writeln!(
                                out,
                                "\tmov {}, {}",
                                reg_name,
                                stack.value(&arg),
                            )?;
                            writeln!(
                                out,
                                "\tmov [rsp+{}], {}",
                                arg_stackpos,
                                reg_name,
                            )?;
                        }
                    }

                    arguments_passed += 1;
                }

                writeln!(out, "\tcall {}", stack.value(&pointer))?;

                if to_layout.size() > 0 {
                    // If it was passed in a register we have to do this, if it was passed by pointer,
                    // then it was written to directly and we're fine.
                    if to_layout.size() <= 8 && to_layout.size().is_power_of_two() {
                        writeln!(out, "\tmov {} {}, {}", name_of_size(to_layout.size()), stack.value(&to), Register::Rax.name(to_layout.size()))?;
                    }
                }
            }
            Instr::MoveImm { to, ref from, size } => {
                for split in split_into_powers_of_two(size) {
                    let mut number = [0_u8; 8];
                    number[..split.size].copy_from_slice(&from[split.offset..split.offset + split.size]);
                    let number = u64::from_le_bytes(number);

                    writeln!(out, "\tmov {} {}, {}", name_of_size(split.size), stack.value_with_offset(&to, split.offset), number)?;
                }
            }
            Instr::Move { to, from, size } => {
                for split in split_into_powers_of_two(size) {
                    let reg_name = Register::Rax.name(split.size);
                    writeln!(out, "\tmov {}, {} {}", reg_name, name_of_size(split.size), stack.value_with_offset(&from, split.offset))?;
                    writeln!(out, "\tmov {} {}, {}", name_of_size(split.size), stack.value_with_offset(&to, split.offset), reg_name)?;
                }
            }
            Instr::StackPtr { to, take_pointer_to } => {
                let reg_name = Register::Rax.name(8);
                writeln!(out, "\tlea {}, {}", reg_name, stack.value(&take_pointer_to))?;
                writeln!(out, "\tmov {}, {}", stack.value(&to), reg_name)?;
            }
            Instr::IncrPtr { to, amount, scale } => {
                let reg_src = Register::Rax.name(8);
                let reg_amount = Register::Rcx.name(8);
                writeln!(out, "\tmov {}, {}", reg_src, stack.value(&to))?;
                writeln!(out, "\tmov {}, {}", reg_amount, stack.value(&amount))?;
                writeln!(out, "\tlea {}, [{}+{}*{}]", reg_src, reg_src, reg_amount, scale)?;
                writeln!(out, "\tmov {}, {}", stack.value(&to), reg_src)?;
            }
            Instr::LabelDefinition(label_id) => {
                writeln!(out, "{}:", label_name(function_id, label_id))?;
            }
            Instr::Unary { to, from, op, type_ } => {
                assert!(!type_.is_float(), "Float operations not handled yet in x64 backend");

                let size = type_.size();
                emit_unary(out, op, &stack, type_, to, RegImmAddr::Stack(from, size), size)?;
            }
            Instr::Binary { to, a, b, op, type_ } => {
                assert!(!type_.is_float(), "Float operations not handled yet in x64 backend");

                let size = type_.size();
                emit_binary(out, op, &stack, type_, to, a, RegImmAddr::Stack(b, size), size)?;
            }
            Instr::BinaryImm { to, a, b, op, type_ } => {
                assert!(!type_.is_float(), "Float operations not handled yet in x64 backend");

                let size = type_.size();
                emit_binary(out, op, &stack, type_, to, a, RegImmAddr::Imm(b, size), size)?;
            }
            Instr::JumpIfZero { condition, to } => {
                writeln!(out, "\tmov al, BYTE {}", stack.value(&condition))?;
                writeln!(out, "\tcmp al, 0")?;
                writeln!(out, "\tje  {}", label_name(function_id, to))?;
            }
            Instr::Jump { to } => {
                writeln!(out, "\tjmp  {}", label_name(function_id, to))?;
            }
            Instr::RefGlobal { to_ptr, global } => {
                writeln!(out, "\tmov rax, {}", global_symbol(global.as_ptr() as usize))?;
                writeln!(out, "\tmov {}, rax", stack.value(&to_ptr))?;
            }
            Instr::IndirectMove { to_ptr, from, size } => {
                writeln!(out, "\tmov rax, {}", stack.value(&to_ptr))?;

                for split in split_into_powers_of_two(size) {
                    let reg_name = Register::Rcx.name(split.size);
                    writeln!(out, "\tmov {}, {} {}", reg_name, name_of_size(split.size), stack.value_with_offset(&from, split.offset))?;
                    writeln!(out, "\tmov {} [rax+{}], {}", name_of_size(split.size), split.offset, reg_name)?;
                }
            }
            Instr::Dereference { to, from_ptr, size } => {
                writeln!(out, "\tmov rax, {}", stack.value(&from_ptr))?;

                for split in split_into_powers_of_two(size) {
                    let reg_name = Register::Rcx.name(split.size);
                    writeln!(out, "\tmov {}, {} [rax+{}]", reg_name, name_of_size(split.size), split.offset)?;
                    writeln!(out, "\tmov {} {}, {}", name_of_size(split.size), stack.value_with_offset(&to, split.offset), reg_name)?;
                }
            }
            Instr::SetToZero { to_ptr, size } => {
                writeln!(out, "\tlea rax, {}", stack.value(&to_ptr))?;

                for split in split_into_powers_of_two(size) {
                    writeln!(out, "\tmov {} [rax+{}], 0", name_of_size(split.size), split.offset)?;
                }
            }
            Instr::ConvertNum { to, from, to_number, from_number } => {
                assert!(!to_number.is_float());
                assert!(!from_number.is_float());

                match to_number.size().cmp(&from_number.size()) {
                    Ordering::Greater => {
                        let needs_sign_extend = to_number.signed() && from_number.signed();

                        let to_reg   = Register::Rax.name(to_number.size());
                        let from_reg = Register::Rcx.name(from_number.size());
                        writeln!(out, "\tmov {}, {}", from_reg, stack.value(&from))?;
                        if needs_sign_extend {
                            writeln!(out, "\tmovsx {}, {}", to_reg, from_reg)?;
                        } else {
                            let to_reg_temp = Register::Rax.name(to_number.size());

                            if from_number.size() == 4 {
                                // Moving a 32bit register to a 64bit register is already a zero extend.
                                // @HACK
                                writeln!(out, "\tmov {}, {}", Register::Rax.name(4), from_reg)?;
                            } else {
                                writeln!(out, "\tmovzx {}, {}", to_reg_temp, from_reg)?;
                            }
                        }

                        writeln!(out, "\tmov {}, {}", stack.value(&to), to_reg)?;
                    }
                    Ordering::Equal => {
                        let reg_name = Register::Rax.name(to_number.size());
                        writeln!(out, "\tmov {}, {}", reg_name, stack.value(&from))?;
                        writeln!(out, "\tmov {}, {}", stack.value(&to), reg_name)?;
                    }
                    Ordering::Less => {
                        let reg_name = Register::Rax.name(to_number.size());
                        writeln!(out, "\tmov {}, {}", reg_name, stack.value(&from))?;
                        writeln!(out, "\tmov {}, {}", stack.value(&to), reg_name)?;
                    }
                }
            }
        }
    }

    if routine.result_layout.size() > 0 {
        if routine.result_layout.size() > 8 || !routine.result_layout.size().is_power_of_two() {
            let to_ptr = stack.offset + 8;
            let from = routine.result;
            writeln!(out, "\tmov rax, [rsp+{}]", to_ptr)?;

            for split in split_into_powers_of_two(routine.result_layout.size()) {
                let reg_name = Register::Rcx.name(split.size);
                writeln!(out, "\tmov {}, {} {}", reg_name, name_of_size(split.size), stack.value_with_offset(&from, split.offset))?;
                writeln!(out, "\tmov {} [rax+{}], {}", name_of_size(split.size), split.offset, reg_name)?;
            }
        } else {
            writeln!(out, "\tmov {}, {}", Register::Rax.name(routine.result_layout.size()), stack.value(&routine.result))?;
        }
    }

    writeln!(out, "\tadd rsp, {}", stack.offset)?;
    writeln!(out, "\tret")?;
    writeln!(out, "{}_end:", function_symbol(function_id))?;

    writeln!(p_data, "\tdd {} wrt ..imagebase", function_symbol(function_id))?;
    writeln!(p_data, "\tdd {}_end wrt ..imagebase", function_symbol(function_id))?;
    writeln!(p_data, "\tdd x_{} wrt ..imagebase", function_symbol(function_id))?;

    let stack_size = stack.offset;
    debug_assert!(stack_size % 8 == 0);

    let num_entries: u8 = if stack_size > 0 {
        if stack_size > 128 {
            2
        } else {
            1
        }
    } else {
        0
    };

    let func_symbol = function_symbol(function_id);
    writeln!(x_data, "x_{func_symbol}:", func_symbol = func_symbol)?;
    writeln!(x_data, "\tdb {code}, ({func_symbol}_prolog_end - {func_symbol}), {num_entries}, 0", func_symbol = func_symbol, num_entries = num_entries, code = 0b0000_0001)?;

    if stack_size > 0 {
        let mut unwind_code: u8 = 0;
        if stack_size > 128 {
            unwind_code |= 1;
            // Only 512K bytes for now
            assert!(stack_size < 512_000);
            unwind_code |= 0 << 4;
            writeln!(x_data, "\tdb 0, {unwind_code}", unwind_code = unwind_code)?;
            writeln!(x_data, "\tdd {}", stack_size / 8)?;
        } else {
            unwind_code |= 2;
            unwind_code |= (((stack_size - 8) / 8) as u8) << 4;
            writeln!(x_data, "\tdb 0, {unwind_code}", unwind_code = unwind_code)?;
            // Ignored code for alignment
            writeln!(x_data, "\tdd 0")?;
        }
    }
    
    Ok(())
}

#[derive(Clone, Copy)]
enum RegImmAddr {
    Reg(Register, usize),
    Stack(Value, usize),
    Imm(u64, usize),
}

impl RegImmAddr {
    //TODO: Create a new enum that doesn't include an immediate value
    fn remove_imm(self, out: &mut String, reg: Register) -> Result<Self, fmt::Error> {
        Ok(match self {
            Self::Imm(num, size) => {
                writeln!(out, "\tmov {}, {}", reg.name(size), num)?;
                Self::Reg(reg, size)
            }
            _ => self,
        })
    }

    fn print<'a>(&'a self, stack: &'a Stack) -> impl fmt::Display + 'a {
        Formatter(move |f| {
            match *self {
                Self::Reg(reg, size) => write!(f, "{}", reg.name(size)),
                Self::Stack(val, size) => write!(f, "{} {}", name_of_size(size), stack.value(&val)),
                Self::Imm(val, size) => write!(f, "{} {}", name_of_size(size), val),
            }
        })
    }
}

fn emit_unary(out: &mut String, op: UnaryOp, stack: &Stack, _type_: PrimitiveType, to: Value, a: RegImmAddr, size: usize) -> fmt::Result {
    let reg_out = Register::Rax.name(size);
    writeln!(out, "\tmov {}, {}", reg_out, a.print(stack))?;
    
    match op {
        UnaryOp::Not => {
            writeln!(out, "\tnot {}", reg_out)?;
        }
        UnaryOp::Negate => {
            writeln!(out, "\tneg {}", reg_out)?;
        }
        _ => writeln!(out, "\t; Unhandled unary operator {:?}", op)?,
    }

    writeln!(out, "\tmov {}, {}", stack.value(&to), reg_out)?;

    Ok(())
}

fn emit_binary(out: &mut String, op: BinaryOp, stack: &Stack, type_: PrimitiveType, to: Value, a: Value, right: RegImmAddr, size: usize) -> fmt::Result {
    let reg_a = Register::Rax.name(size);
    writeln!(out, "\tmov {}, {}", reg_a, stack.value(&a))?;

    match op {
        BinaryOp::Add => {
            writeln!(out, "\tadd {}, {}", reg_a, right.print(stack))?;
            writeln!(out, "\tmov {}, {}", stack.value(&to), reg_a)?;
        }
        BinaryOp::Sub => {
            writeln!(out, "\tsub {}, {}", reg_a, right.print(stack))?;
            writeln!(out, "\tmov {}, {}", stack.value(&to), reg_a)?;
        }
        BinaryOp::Mult => {
            if type_.signed() {
                writeln!(out, "\timul {}", right.print(stack))?;
            } else {
                let right = right.remove_imm(out, Register::R8)?;
                writeln!(out, "\tmul {}", right.print(stack))?;
            }
            writeln!(out, "\tmov {}, {}", stack.value(&to), reg_a)?;
        }
        BinaryOp::Div => {
            let right = right.remove_imm(out, Register::R8)?;
            if type_.signed() {
                writeln!(out, "\tidiv {}", right.print(stack))?;
            } else {
                writeln!(out, "\tdiv {}", right.print(stack))?;
            }
            writeln!(out, "\tmov {}, {}", stack.value(&to), reg_a)?;
        }
        BinaryOp::Equals => {
            writeln!(out, "\tcmp {}, {}", reg_a, right.print(stack))?;
            writeln!(out, "\tsete BYTE {}", stack.value(&to))?;
        }
        BinaryOp::NotEquals => {
            writeln!(out, "\tcmp {}, {}", reg_a, right.print(stack))?;
            writeln!(out, "\tsetne BYTE {}", stack.value(&to))?;
        }
        BinaryOp::LargerThan => {
            writeln!(out, "\tcmp {}, {}", reg_a, right.print(stack))?;
            writeln!(out, "\tsetg BYTE {}", stack.value(&to))?;
        }
        BinaryOp::LargerThanEquals => {
            writeln!(out, "\tcmp {}, {}", reg_a, right.print(stack))?;
            writeln!(out, "\tsetge BYTE {}", stack.value(&to))?;
        }
        BinaryOp::LessThan => {
            writeln!(out, "\tcmp {}, {}", reg_a, right.print(stack))?;
            writeln!(out, "\tsetl BYTE {}", stack.value(&to))?;
        }
        BinaryOp::LessThanEquals => {
            writeln!(out, "\tcmp {}, {}", reg_a, right.print(stack))?;
            writeln!(out, "\tsetle BYTE {}", stack.value(&to))?;
        }
        _ => writeln!(out, "\t; Unhandled binary operator {:?}", op)?,
    }

    Ok(())
}
