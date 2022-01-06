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
    text: String,
}

impl Emitter {
    pub fn emit_routine(
        &mut self, 
        _program: &Program,
        function_id: FunctionId,
        routine: &Routine,
        _args: &[Type],
        _returns: Type,
    ) {
        match routine {
            Routine::UserDefined(routine) => {
                emit_routine(&mut self.text, function_id, routine).unwrap();
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

    let entry = program.get_entry_point().unwrap();
    writeln!(&mut out, "global {}", function_symbol(entry)).unwrap();
    for emitter in &emitters {
        write!(&mut out, "{}", emitter.extern_defs).unwrap();
    }

    writeln!(&mut out, "\nsection .data").unwrap();
    emit_constants(&mut out, program);

    writeln!(&mut out, "\nsection .text").unwrap();

    for emitter in &emitters {
        write!(&mut out, "{}", emitter.text).unwrap();
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

fn emit_routine(
    out: &mut String,
    function_id: FunctionId,
    routine: &UserDefinedRoutine,
) -> fmt::Result {
    writeln!(out, "; {}", routine.name)?;
    writeln!(out, "{}:", function_symbol(function_id))?;

    // @Incomplete: We want to later on track the max alignment used in the stack, and manually align it if it's
    // greater than 16 bytes.
    let stack_size = routine.stack.max;
    let stack_ptr_offset = align_to(stack_size + 8, 16) - 8;

    writeln!(out, "\tsub rsp, {}", stack_ptr_offset)?;

    // @Incomplete: Copy over the arguments from where they were passed

    for instr in &routine.instr {
        writeln!(out, "; {:?}", instr)?;

        match *instr {
            // @Incomplete: Do this
            Instr::DebugLocation(_) => {}
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

                writeln!(out, "\tsub rsp, {}", scratch_region_layout.size())?;

                {
                    let mut scratch_region_layout = StructLayout::new_with_align(0, 16);
                    for &(arg, arg_layout) in args {
                        if arg_layout.size() > 8 || !arg_layout.size().is_power_of_two() {
                            let from = arg;
                            let to = Value(scratch_region_layout.next(arg_layout.layout));
                            for split in split_into_powers_of_two(arg_layout.size()) {
                                let reg_name = Register::Rax.name(split.size);
                                writeln!(out, "\tmov {}, {} [rsp+{}]", reg_name, name_of_size(split.size), from.0 + split.offset)?;
                                writeln!(out, "\tmov {} [rsp+{}], {}", name_of_size(split.size), to.0 + split.offset, reg_name)?;
                            }
                        }
                    }
                }

                writeln!(out, "\tsub rsp, {}", args_layouts.size())?;

                let mut arguments_passed = 0;
                let mut arg_pos = StructLayout::new_with_align(0, 16);
                let mut scratch_region_pos = StructLayout::new_with_align(args_layouts.size(), 16);

                let stack_offset = args_layouts.size() + scratch_region_layout.size();

                // @TODO: Check if it's a float too.
                if to_layout.size() > 8 {
                    // We need to pass a pointer to the return value as the first argument
                    writeln!(
                        out,
                        "\tmov {}, [rsp+{}]",
                        Register::Rcx.name(to_layout.size()),
                        to.0 + stack_offset,
                    )?;

                    arguments_passed += 1;
                    arg_pos.next(to_layout.layout);
                }

                for &(arg, arg_layout) in args.iter() {
                    let reg = [Register::Rcx, Register::Rdx, Register::R8, Register::R9].get(arguments_passed).copied();
                    if arg_layout.size() > 8 || !arg_layout.size().is_power_of_two() {
                        let from_pos = scratch_region_pos.next(arg_layout.layout);

                        if let Some(reg) = reg {
                            arg_pos.next(Layout::U64);
                            writeln!(
                                out,
                                "\tlea {}, [rsp+{}]",
                                reg.name(arg_layout.size()),
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
                        let from_pos = arg.0 + stack_offset;

                        if let Some(reg) = reg {
                            // Registers always seem to take up 64 bits of stack for some reason?
                            arg_pos.next(Layout::U64);

                            writeln!(
                                out,
                                "\tmov {}, [rsp+{}]",
                                reg.name(arg_layout.size()),
                                from_pos,
                            )?;
                        } else {
                            let arg_stackpos = arg_pos.next(arg_layout.layout);

                            let reg_name = Register::Rbx.name(arg_layout.size());
                            writeln!(
                                out,
                                "\tmov {}, [rsp+{}]",
                                reg_name,
                                from_pos,
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

                writeln!(out, "\tcall [rsp+{}]", pointer.0 + stack_offset)?;

                if to_layout.size() > 0 {
                    // If it was passed in a register we have to do this, if it was passed by pointer,
                    // then it was written to directly and we're fine.
                    if to_layout.size() <= 8 && to_layout.size().is_power_of_two() {
                        writeln!(out, "\tmov {} [rsp+{}], {}", name_of_size(to_layout.size()), to.0 + stack_offset, Register::Rax.name(to_layout.size()))?;
                    }
                }

                writeln!(out, "\tadd rsp, {}", stack_offset)?;
            }
            Instr::MoveImm { to, ref from, size } => {
                for split in split_into_powers_of_two(size) {
                    let mut number = [0_u8; 8];
                    number[..split.size].copy_from_slice(&from[split.offset..split.offset + split.size]);
                    let number = u64::from_le_bytes(number);

                    writeln!(out, "\tmov {} [rsp+{}], {}", name_of_size(split.size), to.0 + split.offset, number)?;
                }
            }
            Instr::Move { to, from, size } => {
                for split in split_into_powers_of_two(size) {
                    let reg_name = Register::Rax.name(split.size);
                    writeln!(out, "\tmov {}, {} [rsp+{}]", reg_name, name_of_size(split.size), from.0 + split.offset)?;
                    writeln!(out, "\tmov {} [rsp+{}], {}", name_of_size(split.size), to.0 + split.offset, reg_name)?;
                }
            }
            Instr::StackPtr { to, take_pointer_to } => {
                let reg_name = Register::Rax.name(8);
                writeln!(out, "\tlea {}, [rsp+{}]", reg_name, take_pointer_to.0)?;
                writeln!(out, "\tmov [rsp+{}], {}", to.0, reg_name)?;
            }
            Instr::IncrPtr { to, amount, scale } => {
                let reg_src = Register::Rax.name(8);
                let reg_amount = Register::Rcx.name(8);
                writeln!(out, "\tmov {}, [rsp+{}]", reg_src, to.0)?;
                writeln!(out, "\tmov {}, [rsp+{}]", reg_amount, amount.0)?;
                writeln!(out, "\tlea {}, [{}+{}*{}]", reg_src, reg_src, reg_amount, scale)?;
                writeln!(out, "\tmov [rsp+{}], {}", to.0, reg_src)?;
            }
            Instr::LabelDefinition(label_id) => {
                writeln!(out, "{}:", label_name(function_id, label_id))?;
            }
            Instr::Unary { to, from, op, type_ } => {
                assert!(!type_.is_float(), "Float operations not handled yet in x64 backend");

                let size = type_.size();
                emit_unary(out, op, type_, to, RegImmAddr::Stack(from, size), size)?;
            }
            Instr::Binary { to, a, b, op, type_ } => {
                assert!(!type_.is_float(), "Float operations not handled yet in x64 backend");

                let size = type_.size();
                emit_binary(out, op, type_, to, a, RegImmAddr::Stack(b, size), size)?;
            }
            Instr::BinaryImm { to, a, b, op, type_ } => {
                assert!(!type_.is_float(), "Float operations not handled yet in x64 backend");

                let size = type_.size();
                emit_binary(out, op, type_, to, a, RegImmAddr::Imm(b, size), size)?;
            }
            Instr::JumpIfZero { condition, to } => {
                writeln!(out, "\tmov al, BYTE [rsp+{}]", condition.0)?;
                writeln!(out, "\tcmp al, 0")?;
                writeln!(out, "\tje  {}", label_name(function_id, to))?;
            }
            Instr::Jump { to } => {
                writeln!(out, "\tjmp  {}", label_name(function_id, to))?;
            }
            Instr::RefGlobal { to_ptr, global } => {
                writeln!(out, "\tmov rax, {}", global_symbol(global.as_ptr() as usize))?;
                writeln!(out, "\tmov [rsp+{}], rax", to_ptr.0)?;
            }
            Instr::IndirectMove { to_ptr, from, size } => {
                writeln!(out, "\tmov rax, [rsp+{}]", to_ptr.0)?;

                for split in split_into_powers_of_two(size) {
                    let reg_name = Register::Rcx.name(split.size);
                    writeln!(out, "\tmov {}, {} [rsp+{}]", reg_name, name_of_size(split.size), from.0 + split.offset)?;
                    writeln!(out, "\tmov {} [rax+{}], {}", name_of_size(split.size), split.offset, reg_name)?;
                }
            }
            Instr::Dereference { to, from_ptr, size } => {
                writeln!(out, "\tmov rax, [rsp+{}]", from_ptr.0)?;

                for split in split_into_powers_of_two(size) {
                    let reg_name = Register::Rcx.name(split.size);
                    writeln!(out, "\tmov {}, {} [rax+{}]", reg_name, name_of_size(split.size), split.offset)?;
                    writeln!(out, "\tmov {} [rsp+{}], {}", name_of_size(split.size), to.0 + split.offset, reg_name)?;
                }
            }
            Instr::SetToZero { to_ptr, size } => {
                writeln!(out, "\tmov rax, [rsp+{}]", to_ptr.0)?;

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
                        writeln!(out, "\tmov {}, [rsp+{}]", from_reg, from.0)?;
                        if needs_sign_extend {
                            writeln!(out, "\tmovsx {}, {}", to_reg, from_reg)?;
                        } else {
                            // @HACK: Because moving to eax fills the higher bits with zero, this
                            // is fine.
                            let to_reg_temp = Register::Rax.name(to_number.size().max(4));
                            writeln!(out, "\tmovzx {}, {}", to_reg_temp, from_reg)?;
                        }

                        writeln!(out, "\tmov [rsp+{}], {}", to.0, to_reg)?;
                    }
                    Ordering::Equal => {
                        let reg_name = Register::Rax.name(to_number.size());
                        writeln!(out, "\tmov {}, [rsp+{}]", reg_name, from.0)?;
                        writeln!(out, "\tmov [rsp+{}], {}", to.0, reg_name)?;
                    }
                    Ordering::Less => {
                        let reg_name = Register::Rax.name(to_number.size());
                        writeln!(out, "\tmov {}, [rsp+{}]", reg_name, from.0)?;
                        writeln!(out, "\tmov [rsp+{}], {}", to.0, reg_name)?;
                    }
                }
            }
        }
    }

    writeln!(out, "\tadd rsp, {}", stack_ptr_offset)?;
    writeln!(out, "\tret")?;

    Ok(())
}

#[derive(Clone, Copy)]
enum RegImmAddr {
    Reg(Register, usize),
    Stack(Value, usize),
    Imm(u64, usize),
}

impl fmt::Display for RegImmAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Reg(reg, size) => write!(f, "{}", reg.name(size)),
            Self::Stack(val, size) => write!(f, "{} [rsp+{}]", name_of_size(size), val.0),
            Self::Imm(val, size) => write!(f, "{} {}", name_of_size(size), val),
        }
    }
}

fn emit_unary(out: &mut String, op: UnaryOp, _type_: PrimitiveType, to: Value, a: RegImmAddr, size: usize) -> fmt::Result {
    let reg_out = Register::Rax.name(size);
    writeln!(out, "\tmov {}, {}", reg_out, a)?;
    
    match op {
        UnaryOp::Not => {
            writeln!(out, "\tnot {}", reg_out)?;
        }
        UnaryOp::Negate => {
            writeln!(out, "\tneg {}", reg_out)?;
        }
        _ => writeln!(out, "\t; Unhandled unary operator {:?}", op)?,
    }

    writeln!(out, "\tmov [rsp+{}], {}", to.0, reg_out)?;

    Ok(())
}

fn emit_binary(out: &mut String, op: BinaryOp, type_: PrimitiveType, to: Value, a: Value, right: RegImmAddr, size: usize) -> fmt::Result {
    let reg_a = Register::Rax.name(size);
    writeln!(out, "\tmov {}, [rsp+{}]", reg_a, a.0)?;

    match op {
        BinaryOp::Add => {
            writeln!(out, "\tadd {}, {}", reg_a, right)?;
            writeln!(out, "\tmov [rsp+{}], {}", to.0, reg_a)?;
        }
        BinaryOp::Sub => {
            writeln!(out, "\tsub {}, {}", reg_a, right)?;
            writeln!(out, "\tmov [rsp+{}], {}", to.0, reg_a)?;
        }
        BinaryOp::Mult => {
            if type_.signed() {
                writeln!(out, "\timul {}, {}", reg_a, right)?;
            } else {
                writeln!(out, "\tmul {}, {}", reg_a, right)?;
            }
            writeln!(out, "\tmov [rsp+{}], {}", to.0, reg_a)?;
        }
        BinaryOp::Div => {
            if type_.signed() {
                writeln!(out, "\tidiv {}, {}", reg_a, right)?;
            } else {
                writeln!(out, "\tdiv {}, {}", reg_a, right)?;
            }
            writeln!(out, "\tmov [rsp+{}], {}", to.0, reg_a)?;
        }
        BinaryOp::Equals => {
            writeln!(out, "\tcmp {}, {}", reg_a, right)?;
            writeln!(out, "\tsete BYTE [rsp+{}]", to.0)?;
        }
        BinaryOp::NotEquals => {
            writeln!(out, "\tcmp {}, {}", reg_a, right)?;
            writeln!(out, "\tsetne BYTE [rsp+{}]", to.0)?;
        }
        BinaryOp::LargerThan => {
            writeln!(out, "\tcmp {}, {}", reg_a, right)?;
            writeln!(out, "\tsetg BYTE [rsp+{}]", to.0)?;
        }
        BinaryOp::LargerThanEquals => {
            writeln!(out, "\tcmp {}, {}", reg_a, right)?;
            writeln!(out, "\tsetge BYTE [rsp+{}]", to.0)?;
        }
        BinaryOp::LessThan => {
            writeln!(out, "\tcmp {}, {}", reg_a, right)?;
            writeln!(out, "\tsetl BYTE [rsp+{}]", to.0)?;
        }
        BinaryOp::LessThanEquals => {
            writeln!(out, "\tcmp {}, {}", reg_a, right)?;
            writeln!(out, "\tsetle BYTE [rsp+{}]", to.0)?;
        }
        _ => writeln!(out, "\t; Unhandled binary operator {:?}", op)?,
    }

    Ok(())
}
