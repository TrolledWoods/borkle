use crate::ir::{Instr, UserDefinedRoutine, Routine};
use crate::layout::{align_to, Layout};
use crate::program::{Program, FunctionId};
use crate::types::PointerInType;
use crate::types::Type;
use crate::operators::Operator;
use ustr::Ustr;
use std::path::Path;
use std::fmt::{self, Write};
use super::{Formatter, function_symbol, global_symbol};

#[derive(Default)]
pub struct Emitter {
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
        if let Routine::UserDefined(routine) = routine {
            emit_routine(&mut self.text, function_id, routine).unwrap();
        }
    }
}

pub fn emit(program: &Program, file_path: &Path, emitters: Vec<Emitter>) {
    let mut out = String::new();

    let entry = program.get_entry_point().unwrap();
    writeln!(&mut out, "global {}", function_symbol(entry)).unwrap();

    writeln!(&mut out, "section .data").unwrap();
    emit_constants(&mut out, program);

    writeln!(&mut out, "\n\nsection .text").unwrap();

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
                        write!(out, "{}", function_symbol(ptr_num.into())).unwrap();
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

fn split_into_powers_of_two(mut value: usize) -> impl Iterator<Item = SizeSplit> {
    let mut offset = 0;
    std::iter::from_fn(move || {
        if value == 0 {
            None
        } else if value.is_power_of_two() {
            let size = SizeSplit {
                offset,
                size: value,
            };
            value = 0;
            Some(size)
        } else {
            let current = if value > 8 {
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

                // @Incomplete: Some arguments can be passed on the stack
                let extra_stack_space = 32;

                writeln!(out, "\tsub rsp, {}", extra_stack_space)?;

                for (i, (arg, arg_layout)) in args.iter().enumerate() {
                    assert!(i < 4, "We don't support passing function arguments on the stack yet...");
                    assert!(arg_layout.size <= 8, "Cannot pass large things yet");

                    writeln!(
                        out,
                        "\tmov {}, [rsp+{}]",
                        ["rcx", "rdx", "r8", "r9"][i],
                        arg.0 + extra_stack_space,
                    )?;
                }

                writeln!(out, "\tcall [rsp+{}]", pointer.0 + extra_stack_space)?;

                writeln!(out, "\tmov {} [rsp+{}], {}", name_of_size(to_layout.size), to.0 + extra_stack_space, Register::Rax.name(to_layout.size))?;

                writeln!(out, "\tadd rsp, {}", extra_stack_space)?;
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
            _ => writeln!(out, "\t; -- Unhandled")?,
        }
    }

    writeln!(out, "\tadd rsp, {}", stack_ptr_offset)?;
    writeln!(out, "\tret")?;

    Ok(())
}
