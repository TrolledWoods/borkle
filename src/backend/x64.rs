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
use ustr::{UstrSet, UstrMap};

#[derive(Default)]
struct FileEmitter {
    p_data: String,
    text: String,
}

#[derive(Default)]
pub struct Emitter {
    files: UstrMap<FileEmitter>,
    extern_defs: String,
    x_data: String,
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
                let file_emitter = self.files.entry(routine.loc.file).or_insert_with(Default::default);
                emit_routine(&mut file_emitter.text, &mut self.extern_defs, &mut file_emitter.p_data, &mut self.x_data, program, function_id, routine).unwrap();
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

    writeln!(&mut out, "\nsection .data").unwrap();
    emit_constants(&mut out, program);

    for emitter in &emitters {
        write!(&mut out, "{}", emitter.extern_defs).unwrap();
    }

    // @Performance: This is not fast!
    let files: UstrSet = emitters.iter().flat_map(|v| v.files.keys()).copied().collect();

    writeln!(&mut out, "\nsection .text").unwrap();

    for file in &files {
        for emitter in &emitters {
            if let Some(file_contents) = emitter.files.get(file) {
                write!(&mut out, "{}", file_contents.text).unwrap();
            }
        }
    }

    writeln!(&mut out, "\nsection .pdata rdata align=4").unwrap();

    for file in &files {
        for emitter in &emitters {
            if let Some(file_contents) = emitter.files.get(file) {
                write!(&mut out, "{}", file_contents.p_data).unwrap();
            }
        }
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
    RegCount,
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

fn split_into_powers_of_two_with_max(mut value: usize, max: usize) -> impl Iterator<Item = SizeSplit> {
    let mut offset = 0;
    std::iter::from_fn(move || {
        if value == 0 {
            None
        } else if value <= max && value.is_power_of_two() {
            let size = SizeSplit {
                offset,
                size: value,
            };
            value = 0;
            Some(size)
        } else {
            let current = if value >= max {
                max
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

fn split_into_powers_of_two(value: usize) -> impl Iterator<Item = SizeSplit> {
    split_into_powers_of_two_with_max(value, 8)
}

/*struct AllocatedRegister {
    stack_pos: usize,
    size: u8,
}

#[derive(Default)]
struct Registers {
    allocated: [Option<AllocatedRegister>; Register::RegCount as u8 as usize],
}*/

struct Context<'a> {
    out: &'a mut String,
    stack: Stack,
}

struct Stack {
    offset: usize,
    stack_size: usize,
}

impl Stack {
    fn variables_base(&self) -> usize {
        self.offset - self.stack_size
    }

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
        writeln!(out, "%line {:0>3}+000 {}", loc.line, loc.file)?;

        // writeln!(extern_defs, "%line {:0>3}+000 {}", loc.line, loc.file)?;
        // writeln!(p_data, "%line {:0>3}+000 {}", loc.line, loc.file)?;
        // writeln!(x_data, "%line {:0>3}+000 {}", loc.line, loc.file)?;
    }

    writeln!(extern_defs, "global {}", function_symbol(function_id)).unwrap();

    writeln!(out, "; {}", routine.name)?;
    writeln!(out, "{}:", function_symbol(function_id))?;

    // @Incomplete: We want to later on track the max alignment used in the stack, and manually align it if it's
    // greater than 16 bytes.
    let stack_size = align_to(routine.stack.max + 8, 16) - 8;

    let mut ctx = Context {
        out,
        stack: Stack {
            offset: stack_size,
            stack_size,
        },
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
    ctx.stack.offset += function_args_offset;

    writeln!(ctx.out, "\tsub rsp, {}", ctx.stack.offset)?;

    writeln!(ctx.out, "{}_prolog_end:", function_symbol(function_id))?;

    {
        // @Incomplete: Copy over the arguments from where they were passed
        // Do this to ignore the return function pointer that's also on the stack at this point.
        let mut to_stack = StructLayout::new(ctx.stack.variables_base());
        let mut arg_pos = StructLayout::new_with_align(ctx.stack.offset + 8, 16);
        let mut args_read = 0;

        if routine.result_layout.size() > 0 && (routine.result_layout.size() > 8 || !routine.result_layout.size().is_power_of_two()) {
            let stack_pos = arg_pos.next(Layout::PTR);
            writeln!(
                ctx.out,
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
                        ctx.out,
                        "\tlea rcx, [rsp+{}]",
                        stack_pos,
                    )?;
                    Register::Rcx
                };

                let write_to = to_stack.next(arg_layout.layout);
                for split in split_into_powers_of_two(arg_layout.size()) {
                    let reg_name = Register::Rax.name(split.size);
                    writeln!(ctx.out, "\tmov {}, {} [{}+{}]", reg_name, name_of_size(split.size), reg.name(8), split.offset)?;
                    writeln!(ctx.out, "\tmov {} [rsp+{}], {}", name_of_size(split.size), write_to + split.offset, reg_name)?;
                }
            } else {
                let write_to = to_stack.next(arg_layout.layout);

                if let Some(reg) = reg {
                    arg_pos.next(Layout::U64);
                    writeln!(
                        ctx.out,
                        "\tmov [rsp+{}], {}",
                        write_to,
                        reg.name(arg_layout.size()),
                    )?;
                } else {
                    let stack_pos = arg_pos.next(arg_layout.layout);
                    let reg_name = Register::Rcx.name(arg_layout.size());
                    writeln!(
                        ctx.out,
                        "\tmov {}, [rsp+{}]",
                        reg_name,
                        stack_pos,
                    )?;
                    writeln!(
                        ctx.out,
                        "\tmov [rsp+{}], {}",
                        write_to,
                        reg_name,
                    )?;
                }
            }

            args_read += 1;
        }
    }

    for instr in &routine.instr {
        match *instr {
            Instr::DebugLocation(loc) => {
                if is_debugging {
                    writeln!(ctx.out, "%line {:0>3}+000 {}", loc.line, loc.file)?;
                }
            }
            Instr::Call { to: (to, to_layout), pointer, ref args, loc: _ } => {
                // @Incomplete: We want to look at which calling convention we're using here too,
                // for now we just assume the standard x64 convention

                let mut args_layouts = StructLayout::new_with_align(0, 16);
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
                                writeln!(ctx.out, "\tmov {}, {} {}", reg_name, name_of_size(split.size), ctx.stack.value_with_offset(&from, split.offset))?;
                                writeln!(ctx.out, "\tmov {} [rsp+{}], {}", name_of_size(split.size), to + split.offset, reg_name)?;
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
                        ctx.out,
                        "\nlea {}, {}",
                        Register::Rcx.name(8),
                        ctx.stack.value(&to)
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
                                ctx.out,
                                "\tlea {}, [rsp+{}]",
                                reg.name(8),
                                from_pos,
                            )?;
                        } else {
                            let arg_stackpos = arg_pos.next(Layout::PTR);
                            // @Correctness: `rbx` is non-volatile, we shouldn't modify it.
                            writeln!(
                                ctx.out,
                                "\tlea rax, [rsp+{}]",
                                from_pos,
                            )?;
                            writeln!(
                                ctx.out,
                                "\tmov [rsp+{}], rax",
                                arg_stackpos,
                            )?;
                        }
                    } else {
                        if let Some(reg) = reg {
                            // Registers always seem to take up 64 bits of stack for some reason?
                            arg_pos.next(Layout::U64);

                            writeln!(
                                ctx.out,
                                "\tmov {}, {}",
                                reg.name(arg_layout.size()),
                                ctx.stack.value(&arg),
                            )?;
                        } else {
                            let arg_stackpos = arg_pos.next(arg_layout.layout);

                            let reg_name = Register::Rax.name(arg_layout.size());
                            writeln!(
                                ctx.out,
                                "\tmov {}, {}",
                                reg_name,
                                ctx.stack.value(&arg),
                            )?;
                            writeln!(
                                ctx.out,
                                "\tmov [rsp+{}], {}",
                                arg_stackpos,
                                reg_name,
                            )?;
                        }
                    }

                    arguments_passed += 1;
                }

                writeln!(ctx.out, "\tcall {}", ctx.stack.value(&pointer))?;

                if is_debugging {
                    // Too make the call stack point to the actual call, and not the line after.
                    writeln!(ctx.out, "\tnop")?;
                }

                if to_layout.size() > 0 {
                    // If it was passed in a register we have to do this, if it was passed by pointer,
                    // then it was written to directly and we're fine.
                    if to_layout.size() <= 8 && to_layout.size().is_power_of_two() {
                        writeln!(ctx.out, "\tmov {} {}, {}", name_of_size(to_layout.size()), ctx.stack.value(&to), Register::Rax.name(to_layout.size()))?;
                    }
                }
            }
            Instr::MoveImm { to, ref from, size } => {
                for split in split_into_powers_of_two_with_max(size, 4) {
                    let mut number = [0_u8; 4];
                    number[..split.size].copy_from_slice(&from[split.offset..split.offset + split.size]);
                    let number = u32::from_le_bytes(number);

                    writeln!(ctx.out, "\tmov {} {}, {}", name_of_size(split.size), ctx.stack.value_with_offset(&to, split.offset), number)?;
                }
            }
            Instr::Move { to, from, size } => {
                for split in split_into_powers_of_two(size) {
                    let reg_name = Register::Rax.name(split.size);
                    writeln!(ctx.out, "\tmov {}, {} {}", reg_name, name_of_size(split.size), ctx.stack.value_with_offset(&from, split.offset))?;
                    writeln!(ctx.out, "\tmov {} {}, {}", name_of_size(split.size), ctx.stack.value_with_offset(&to, split.offset), reg_name)?;
                }
            }
            Instr::StackPtr { to, take_pointer_to } => {
                let reg_name = Register::Rax.name(8);
                writeln!(ctx.out, "\tlea {}, {}", reg_name, ctx.stack.value(&take_pointer_to))?;
                writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_name)?;
            }
            Instr::IncrPtr { to, amount, scale } => {
                let reg_src = Register::Rcx.name(8);
                let reg_amount = Register::Rax.name(8);
                writeln!(ctx.out, "\tmov {}, {}", reg_src, ctx.stack.value(&to))?;
                writeln!(ctx.out, "\tmov {}, {}", reg_amount, ctx.stack.value(&amount))?;
                match scale {
                    1 => writeln!(ctx.out, "\tlea {}, [{}+{}]", reg_src, reg_src, reg_amount)?,
                    2 | 4 | 8 => writeln!(ctx.out, "\tlea {}, [{}+{}*{}]", reg_src, reg_src, reg_amount, scale)?,
                    _ => {
                        let reg_temp_scale = Register::Rdx.name(8);
                        writeln!(ctx.out, "\tmov {}, {}", reg_temp_scale, scale)?;
                        writeln!(ctx.out, "\tmul {}", reg_temp_scale)?;
                        writeln!(ctx.out, "\tlea {}, [{}+{}]", reg_src, reg_src, reg_amount)?;
                    },
                }
                writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_src)?;
            }
            Instr::LabelDefinition(label_id) => {
                writeln!(ctx.out, "{}:", label_name(function_id, label_id))?;
            }
            Instr::Unary { to, from, op, type_ } => {
                assert!(!type_.is_float(), "Float operations not handled yet in x64 backend");

                let size = type_.size();
                emit_unary(&mut ctx, op, type_, to, RegImmAddr::Stack(from, size), size)?;
            }
            Instr::Binary { to, a, b, op, type_ } => {
                assert!(!type_.is_float(), "Float operations not handled yet in x64 backend");

                let size = type_.size();
                emit_binary(&mut ctx, op, type_, to, a, RegImmAddr::Stack(b, size), size)?;
            }
            Instr::BinaryImm { to, a, b, op, type_ } => {
                assert!(!type_.is_float(), "Float operations not handled yet in x64 backend");

                let size = type_.size();
                emit_binary(&mut ctx, op, type_, to, a, RegImmAddr::Imm(b, size), size)?;
            }
            Instr::JumpIfZero { condition, to } => {
                writeln!(ctx.out, "\tmov al, BYTE {}", ctx.stack.value(&condition))?;
                writeln!(ctx.out, "\tcmp al, 0")?;
                writeln!(ctx.out, "\tje  {}", label_name(function_id, to))?;
            }
            Instr::Jump { to } => {
                writeln!(ctx.out, "\tjmp  {}", label_name(function_id, to))?;
            }
            Instr::RefGlobal { to_ptr, global } => {
                writeln!(ctx.out, "\tmov rax, {}", global_symbol(global.as_ptr() as usize))?;
                writeln!(ctx.out, "\tmov {}, rax", ctx.stack.value(&to_ptr))?;
            }
            Instr::IndirectMove { to_ptr, from, size } => {
                writeln!(ctx.out, "\tmov rax, {}", ctx.stack.value(&to_ptr))?;

                for split in split_into_powers_of_two(size) {
                    let reg_name = Register::Rcx.name(split.size);
                    writeln!(ctx.out, "\tmov {}, {} {}", reg_name, name_of_size(split.size), ctx.stack.value_with_offset(&from, split.offset))?;
                    writeln!(ctx.out, "\tmov {} [rax+{}], {}", name_of_size(split.size), split.offset, reg_name)?;
                }
            }
            Instr::Dereference { to, from_ptr, size } => {
                writeln!(ctx.out, "\tmov rax, {}", ctx.stack.value(&from_ptr))?;

                for split in split_into_powers_of_two(size) {
                    let reg_name = Register::Rcx.name(split.size);
                    writeln!(ctx.out, "\tmov {}, {} [rax+{}]", reg_name, name_of_size(split.size), split.offset)?;
                    writeln!(ctx.out, "\tmov {} {}, {}", name_of_size(split.size), ctx.stack.value_with_offset(&to, split.offset), reg_name)?;
                }
            }
            Instr::SetToZero { to_ptr, size } => {
                writeln!(ctx.out, "\tlea rax, {}", ctx.stack.value(&to_ptr))?;

                for split in split_into_powers_of_two(size) {
                    writeln!(ctx.out, "\tmov {} [rax+{}], 0", name_of_size(split.size), split.offset)?;
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
                        writeln!(ctx.out, "\tmov {}, {}", from_reg, ctx.stack.value(&from))?;
                        if needs_sign_extend {
                            writeln!(ctx.out, "\tmovsx {}, {}", to_reg, from_reg)?;
                        } else {
                            let to_reg_temp = Register::Rax.name(to_number.size());

                            if from_number.size() == 4 {
                                // Moving a 32bit register to a 64bit register is already a zero extend.
                                // @HACK
                                writeln!(ctx.out, "\tmov {}, {}", Register::Rax.name(4), from_reg)?;
                            } else {
                                writeln!(ctx.out, "\tmovzx {}, {}", to_reg_temp, from_reg)?;
                            }
                        }

                        writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), to_reg)?;
                    }
                    Ordering::Equal => {
                        let reg_name = Register::Rax.name(to_number.size());
                        writeln!(ctx.out, "\tmov {}, {}", reg_name, ctx.stack.value(&from))?;
                        writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_name)?;
                    }
                    Ordering::Less => {
                        let reg_name = Register::Rax.name(to_number.size());
                        writeln!(ctx.out, "\tmov {}, {}", reg_name, ctx.stack.value(&from))?;
                        writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_name)?;
                    }
                }
            }
        }
    }

    if routine.result_layout.size() > 0 {
        if routine.result_layout.size() > 8 || !routine.result_layout.size().is_power_of_two() {
            let to_ptr = ctx.stack.offset + 8;
            let from = routine.result;
            writeln!(ctx.out, "\tmov rax, [rsp+{}]", to_ptr)?;

            for split in split_into_powers_of_two(routine.result_layout.size()) {
                let reg_name = Register::Rcx.name(split.size);
                writeln!(ctx.out, "\tmov {}, {} {}", reg_name, name_of_size(split.size), ctx.stack.value_with_offset(&from, split.offset))?;
                writeln!(ctx.out, "\tmov {} [rax+{}], {}", name_of_size(split.size), split.offset, reg_name)?;
            }
        } else {
            writeln!(ctx.out, "\tmov {}, {}", Register::Rax.name(routine.result_layout.size()), ctx.stack.value(&routine.result))?;
        }
    }

    writeln!(ctx.out, "\tadd rsp, {}", ctx.stack.offset)?;
    writeln!(ctx.out, "\tret")?;
    writeln!(ctx.out, "{}_end:", function_symbol(function_id))?;

    writeln!(p_data, "\tdd {} wrt ..imagebase", function_symbol(function_id))?;
    writeln!(p_data, "\tdd {}_end wrt ..imagebase", function_symbol(function_id))?;
    writeln!(p_data, "\tdd x_{} wrt ..imagebase", function_symbol(function_id))?;

    let stack_size = ctx.stack.offset;
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
            writeln!(x_data, "\tdb ({func_symbol}_prolog_end - {func_symbol}), {unwind_code}", func_symbol = func_symbol, unwind_code = unwind_code)?;
            writeln!(x_data, "\tdw {}", stack_size / 8)?;
        } else {
            unwind_code |= 2;
            unwind_code |= (((stack_size - 8) / 8) as u8) << 4;
            writeln!(x_data, "\tdb ({func_symbol}_prolog_end - {func_symbol}), {unwind_code}", func_symbol = func_symbol, unwind_code = unwind_code)?;
            // Ignored code for alignment
            writeln!(x_data, "\tdw 0")?;
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

    fn reduce_size(self, out: &mut String, imm_reg: Register, max_size: usize) -> Result<Self, fmt::Error> {
        Ok(match self {
            Self::Imm(num, size) if size > max_size => {
                if num < 2_u64.pow(max_size as u32 * 8 - 1) {
                    Self::Imm(num, max_size)
                } else {
                    writeln!(out, "\tmov {}, {}", imm_reg.name(size), num)?;
                    Self::Reg(imm_reg, size)
                }
            }
            Self::Stack(value, size) if size > max_size => {
                Self::Stack(value, max_size)
            }
            Self::Reg(reg, size) if size > max_size => {
                Self::Reg(reg, max_size)
            }
            _ => self,
        })
    }

    fn reduce_immediate_size(self, out: &mut String, imm_reg: Register, max_size: usize) -> Result<Self, fmt::Error> {
        Ok(match self {
            Self::Imm(num, size) if size > max_size => {
                if num < 2_u64.pow(max_size as u32 * 8 - 1) {
                    Self::Imm(num, max_size)
                } else {
                    writeln!(out, "\tmov {}, {}", imm_reg.name(size), num)?;
                    Self::Reg(imm_reg, max_size)
                }
            }
            _ => self,
        })
    }

    fn print<'a>(&'a self, stack: &'a Stack) -> impl fmt::Display + 'a {
        Formatter(move |f| {
            match *self {
                Self::Reg(reg, size) => write!(f, "{}", reg.name(size)),
                Self::Stack(val, size) => write!(f, "{} {}", name_of_size(size), stack.value(&val)),
                Self::Imm(val, _size) => write!(f, "{}", val),
            }
        })
    }
}

fn emit_unary(ctx: &mut Context<'_>, op: UnaryOp, type_: PrimitiveType, to: Value, a: RegImmAddr, size: usize) -> fmt::Result {
    let reg_out = Register::Rax.name(size);

    let a = a.reduce_immediate_size(ctx.out, Register::R8, 4)?;
    writeln!(ctx.out, "\tmov {}, {}", reg_out, a.print(&ctx.stack))?;
    
    match op {
        UnaryOp::Not => {
            if matches!(type_, PrimitiveType::Bool) {
                let a = a.remove_imm(ctx.out, Register::R8)?;
                writeln!(ctx.out, "\tcmp {}, 0", a.print(&ctx.stack))?;
                writeln!(ctx.out, "\tsete {}", reg_out)?;
            } else {
                writeln!(ctx.out, "\tnot {}", reg_out)?;
            }
        }
        UnaryOp::Negate => {
            writeln!(ctx.out, "\tneg {}", reg_out)?;
        }
        _ => {
            writeln!(ctx.out, "\t; Unhandled unary operator {:?}", op)?;
            println!("\t; Unhandled unary operator {:?}", op);
        }
    }

    writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_out)?;

    Ok(())
}

fn emit_binary(ctx: &mut Context<'_>, op: BinaryOp, type_: PrimitiveType, to: Value, a: Value, right: RegImmAddr, size: usize) -> fmt::Result {
    let reg_a = Register::Rax.name(size);
    writeln!(ctx.out, "\tmov {}, {}", reg_a, ctx.stack.value(&a))?;

    let right = right.reduce_immediate_size(ctx.out, Register::R8, 4)?;

    match op {
        BinaryOp::Add => {
            writeln!(ctx.out, "\tadd {}, {}", reg_a, right.print(&ctx.stack))?;
            writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_a)?;
        }
        BinaryOp::Sub => {
            writeln!(ctx.out, "\tsub {}, {}", reg_a, right.print(&ctx.stack))?;
            writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_a)?;
        }
        BinaryOp::Mult => {
            if type_.signed() {
                writeln!(ctx.out, "\timul {}", right.print(&ctx.stack))?;
            } else {
                let right = right.remove_imm(ctx.out, Register::R8)?;
                writeln!(ctx.out, "\tmul {}", right.print(&ctx.stack))?;
            }
            writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_a)?;
        }
        BinaryOp::Div => {
            // @Note: Remainder is stored in RDX
            let right = right.remove_imm(ctx.out, Register::R8)?;
            if type_.signed() {
                match size {
                    1 => writeln!(ctx.out, "\tmovsx ax, al")?,
                    2 => writeln!(ctx.out, "\tcwd")?,
                    4 => writeln!(ctx.out, "\tcdq")?,
                    8 => writeln!(ctx.out, "\tcqo")?,
                    _ => unreachable!(),
                }
                writeln!(ctx.out, "\tidiv {}", right.print(&ctx.stack))?;
            } else {
                if size == 1 {
                    writeln!(ctx.out, "\txor ah, ah")?;
                } else {
                    writeln!(ctx.out, "\txor {reg_name:}, {reg_name:}", reg_name = Register::Rdx.name(size))?;
                }
                writeln!(ctx.out, "\tdiv {}", right.print(&ctx.stack))?;
            }

            writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_a)?;
        }
        BinaryOp::Modulo => {
            // @Note: Normal value is stored in EAX, remainder is stored in RDX
            let right = right.remove_imm(ctx.out, Register::R8)?;
            if type_.signed() {
                match size {
                    1 => writeln!(ctx.out, "\tmovsx ax, al")?,
                    2 => writeln!(ctx.out, "\tcwd")?,
                    4 => writeln!(ctx.out, "\tcdq")?,
                    8 => writeln!(ctx.out, "\tcqo")?,
                    _ => unreachable!(),
                }
                writeln!(ctx.out, "\tidiv {}", right.print(&ctx.stack))?;
            } else {
                writeln!(ctx.out, "\txor {reg_name:}, {reg_name:}", reg_name = Register::Rdx.name(size))?;
                writeln!(ctx.out, "\tdiv {}", right.print(&ctx.stack))?;
            }

            if size == 1 {
                writeln!(ctx.out, "\tmov {}, ah", ctx.stack.value(&to))?;
            } else {
                writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), Register::Rdx.name(size))?;
            }
        }
        BinaryOp::ShiftLeft => {
            let right = right.reduce_size(ctx.out, Register::R8, 1)?;
            writeln!(ctx.out, "\tmov cl, {}", right.print(&ctx.stack))?;
            writeln!(ctx.out, "\tshl {}, cl", reg_a)?;
            writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_a)?;
        }
        BinaryOp::ShiftRight => {
            let right = right.reduce_size(ctx.out, Register::R8, 1)?;
            writeln!(ctx.out, "\tmov cl, {}", right.print(&ctx.stack))?;
            writeln!(ctx.out, "\tsar {}, cl", reg_a)?;
            writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_a)?;
        }
        BinaryOp::Equals => {
            writeln!(ctx.out, "\tcmp {}, {}", reg_a, right.print(&ctx.stack))?;
            writeln!(ctx.out, "\tsete BYTE {}", ctx.stack.value(&to))?;
        }
        BinaryOp::NotEquals => {
            writeln!(ctx.out, "\tcmp {}, {}", reg_a, right.print(&ctx.stack))?;
            writeln!(ctx.out, "\tsetne BYTE {}", ctx.stack.value(&to))?;
        }
        BinaryOp::LargerThan => {
            writeln!(ctx.out, "\tcmp {}, {}", reg_a, right.print(&ctx.stack))?;
            if type_.signed() {
                writeln!(ctx.out, "\tsetg BYTE {}", ctx.stack.value(&to))?;
            } else {
                writeln!(ctx.out, "\tseta BYTE {}", ctx.stack.value(&to))?;
            }
        }
        BinaryOp::LargerThanEquals => {
            writeln!(ctx.out, "\tcmp {}, {}", reg_a, right.print(&ctx.stack))?;
            if type_.signed() {
                writeln!(ctx.out, "\tsetge BYTE {}", ctx.stack.value(&to))?;
            } else {
                writeln!(ctx.out, "\tsetae BYTE {}", ctx.stack.value(&to))?;
            }
        }
        BinaryOp::LessThan => {
            writeln!(ctx.out, "\tcmp {}, {}", reg_a, right.print(&ctx.stack))?;
            if type_.signed() {
                writeln!(ctx.out, "\tsetl BYTE {}", ctx.stack.value(&to))?;
            } else {
                writeln!(ctx.out, "\tsetb BYTE {}", ctx.stack.value(&to))?;
            }
        }
        BinaryOp::LessThanEquals => {
            writeln!(ctx.out, "\tcmp {}, {}", reg_a, right.print(&ctx.stack))?;
            if type_.signed() {
                writeln!(ctx.out, "\tsetle BYTE {}", ctx.stack.value(&to))?;
            } else {
                writeln!(ctx.out, "\tsetbe BYTE {}", ctx.stack.value(&to))?;
            }
        }
        BinaryOp::And | BinaryOp::BitAnd => {
            writeln!(ctx.out, "\tand {}, {}", reg_a, right.print(&ctx.stack))?;
            writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_a)?;
        }
        BinaryOp::Or | BinaryOp::BitOr => {
            writeln!(ctx.out, "\tor {}, {}", reg_a, right.print(&ctx.stack))?;
            writeln!(ctx.out, "\tmov {}, {}", ctx.stack.value(&to), reg_a)?;
        }
        _ => {
            writeln!(ctx.out, "\t; Unhandled binary operator {:?}", op)?;
            println!("\t; Unhandled binary operator {:?}", op);
        }
    }

    Ok(())
}
