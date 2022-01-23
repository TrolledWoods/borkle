use crate::ir::{Instr, UserDefinedRoutine, Routine, LabelId, PrimitiveType, StackValue};
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

const DEBUG_SPAM: bool = false;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

#[derive(Debug, Clone, Copy)]
struct ReferencedStackValue {
    stack_offset: usize,
    size: usize,
    updated: bool,
}

#[derive(Default, Debug)]
struct AllocatedRegister {
    /// This refers to if this register contains a stack value.
    /// If the `updated` flag is set, this contains a newer version of the stack value than
    /// what exists on the stack. There should never be two updated registers to the same
    /// stack location at once.
    referenced_stack_value: Option<ReferencedStackValue>,
    last_usage: u32,
    in_use: bool,
}

// For now, this only includes volatile registers, because it's a little tricky to
// store non-volatile registers on the stack with the system I have right now.
const AVAILABLE_REGISTERS: &[Register] = &[Register::Rax, Register::Rcx, Register::Rdx, Register::R8, Register::R9, Register::R10, Register::R11];

#[derive(Default, Debug)]
struct Registers {
    allocated: [AllocatedRegister; Register::RegCount as u8 as usize],
    usage_ctr: u32,
}

impl Registers {
    fn mark_as_updated(&mut self, id: Register) {
        let register = &mut self.allocated[id as u8 as usize];
        if let Some(stack_value) = &mut register.referenced_stack_value {
            stack_value.updated = true;
        }
    }
}

impl Register {
    fn name(self, size: usize) -> &'static str {
        match (self, size) {
            (Register::Rax, 1) =>  "al",
            (Register::Rax, 2) =>  "ax",
            (Register::Rax, 4) => "eax",
            (Register::Rax, 8) => "rax",
            (Register::Rbx, 1) =>  "bl",
            (Register::Rbx, 2) =>  "bx",
            (Register::Rbx, 4) => "ebx",
            (Register::Rbx, 8) => "rbx",
            (Register::Rcx, 1) =>  "cl",
            (Register::Rcx, 2) =>  "cx",
            (Register::Rcx, 4) => "ecx",
            (Register::Rcx, 8) => "rcx",
            (Register::Rdx, 1) =>  "dl",
            (Register::Rdx, 2) =>  "dx",
            (Register::Rdx, 4) => "edx",
            (Register::Rdx, 8) => "rdx",
            (Register::R8, 1) => "r8b",
            (Register::R8, 2) => "r8w",
            (Register::R8, 4) => "r8d",
            (Register::R8, 8) => "r8",
            (Register::R9, 1) => "r9b",
            (Register::R9, 2) => "r9w",
            (Register::R9, 4) => "r9d",
            (Register::R9, 8) => "r9",
            (Register::R10, 1) => "r10b",
            (Register::R10, 2) => "r10w",
            (Register::R10, 4) => "r10d",
            (Register::R10, 8) => "r10",
            (Register::R11, 1) => "r11b",
            (Register::R11, 2) => "r11w",
            (Register::R11, 4) => "r11d",
            (Register::R11, 8) => "r11",
            (reg, size) => unreachable!("Invalid combination of register and size, {:?}, size {}", reg, size),
        }
    }
}

struct Context<'a> {
    out: &'a mut String,
    stack: Stack,
    registers: Registers,
}

impl Context<'_> {
    /// Pushes the value of a register to the stack.
    /// Does not invalidate the register, so only do this if you need to read from the stack later.
    fn push_reg_changes(&mut self, reg_id: Register) -> fmt::Result {
        let register = &mut self.registers.allocated[reg_id as u8 as usize];
        if DEBUG_SPAM { writeln!(self.out, "; Trying to push reg changes for {}", reg_id.name(8))?; }

        if let Some(referenced_value) = &mut register.referenced_stack_value {
            if referenced_value.updated {
                if DEBUG_SPAM { writeln!(self.out, "; Pushed reg changes for {}", reg_id.name(8))?; }
                writeln!(self.out, "\tmov [rsp+{}], {}", referenced_value.stack_offset, reg_id.name(referenced_value.size))?;
                referenced_value.updated = false;
            }
        }

        Ok(())
    }

    fn push_all_changes(&mut self) -> fmt::Result {
        for &id in AVAILABLE_REGISTERS {
            self.push_reg_changes(id)?;
        }

        Ok(())
    }

    fn flush(&mut self, reg_id: Register) -> fmt::Result {
        let register = &mut self.registers.allocated[reg_id as u8 as usize];

        if let Some(referenced_value) = register.referenced_stack_value.take() {
            if referenced_value.updated {
                writeln!(self.out, "\tmov [rsp+{}], {}", referenced_value.stack_offset, reg_id.name(referenced_value.size))?;
            }
        }

        Ok(())
    }

    fn flush_all(&mut self) -> fmt::Result {
        if DEBUG_SPAM { writeln!(self.out, "\t; FLUSH!!!!! Culprit: {}", std::panic::Location::caller())?; }
        for &id in AVAILABLE_REGISTERS {
            self.flush(id)?;
        }

        Ok(())
    }

    fn emit_reg(&mut self, op_name: &str, reg: Register, size: usize) -> fmt::Result {
        self.push_reg_changes(reg)?;
        writeln!(self.out, "\t{} {}", op_name, reg.name(size))?;
        self.reg_written_to(reg);

        Ok(())
    }

    fn emit_write(&mut self, op_name: &str, a: Register, size: usize,) -> fmt::Result {
        self.push_reg_changes(a)?;
        writeln!(self.out, "\t{} {}", op_name, a.name(size))?;
        self.reg_written_to(a);

        Ok(())
    }

    fn emit_dat(&mut self, op_name: &str, a: DataHandle) -> fmt::Result {
        writeln!(self.out, "\t{} {}", op_name, a.print(&self.stack))?;

        Ok(())
    }

    fn emit_write_dat(&mut self, op_name: &str, a: Register, size: usize, b: DataHandle) -> fmt::Result {
        self.push_reg_changes(a)?;
        writeln!(self.out, "\t{} {}, {}", op_name, a.name(size), b.print(&self.stack))?;
        self.reg_written_to(a);

        Ok(())
    }

    fn emit_dat_dat(&mut self, op_name: &str, a: DataHandle, b: DataHandle) -> fmt::Result {
        writeln!(self.out, "\t{} {}, {}", op_name, a.print(&self.stack), b.print(&self.stack))?;

        Ok(())
    }

    fn get_data_as_reg(&mut self, wanted_data: Data) -> Result<Register, fmt::Error> {
        let DataHandle::Reg(handle, _) = self.get_data(wanted_data, 0)? else {
            unreachable!("Our allowances don't allow for anything but an owned register here!")
        };
        Ok(handle)
    }

    /// Reads data for use in a "single instruction". Might allocate a register,
    /// so make sure there's enough registers left over for this.
    fn get_data(&mut self, wanted_data: Data, allowed_data: AllowedDataFlags) -> Result<DataHandle, fmt::Error> {
        match wanted_data {
            Data::Reg(reg, size) => {
                let new = self.alloc_reg()?;
                self.emit_write_dat("mov", reg, size, DataHandle::Reg(reg, size))?;
                Ok(DataHandle::Reg(new, size))
            }
            Data::Stack(value, size) => {
                let new = self.alloc_reg_with_stack_value(value, size)?;
                if let Some(reg) = new {
                    Ok(DataHandle::Reg(reg, size))
                // TODO: This should be reenabled later, but I don't have good enough heuristics
                // to tell what benefits from going in a register or not, and this is just circumstancial,
                // which is pretty bad, so I just don't enable it.
                //
                // } else if allowed_data & ALLOWED_DATA_FLAG_INDIRECT > 0 {
                //  Ok(DataHandle::Stack(value, size))
                } else {
                    let stack_offset = self.stack.get_stack_offset(&value);
                    let reg = self.alloc_reg()?;
                    self.flush(reg)?;
                    writeln!(self.out, "\tmov {}, {} [rsp+{}]", reg.name(size), name_of_size(size), stack_offset)?;

                    self.registers.allocated[reg as u8 as usize].referenced_stack_value = Some(ReferencedStackValue {
                        stack_offset,
                        size,
                        updated: false,
                    });

                    Ok(DataHandle::Reg(reg, size))
                }
            }
            Data::Imm(value, size) => {
                let allowed_size = (allowed_data & ALLOWED_DATA_FLAG_MAX_IMM_SIZE) as u32;

                // TODO: Eventually, I'd like to allow for setting any immediate size you want separately.
                // We have to allocate a register if the value does not fit in the allowed size.
                if allowed_size == 0 || ((allowed_size as usize) < size && value >= (2_u64.pow(allowed_size * 8 - 1))) {
                    let reg = self.alloc_reg()?;
                    self.emit_write_dat("mov", reg, size, DataHandle::Imm(value, size))?;
                    return Ok(DataHandle::Reg(reg, size));
                }

                Ok(DataHandle::Imm(value, size))
            }
        }
    }

    fn free_reg(&mut self, reg: Register) {
        let register = &mut self.registers.allocated[reg as u8 as usize];
        register.in_use = false;
    }

    fn free_all(&mut self) {
        for allocated in &mut self.registers.allocated {
            allocated.in_use = false;
        }
    }

    /// Purges any notion that a register references an overlapping section of the stack.
    fn purge_stack_value(&mut self, stack_offset: usize, size: usize) -> fmt::Result {
        if DEBUG_SPAM { writeln!(self.out, "; Purge stack offset {}, size {}", stack_offset, size)?; }
        for allocated in &mut self.registers.allocated {
            if let Some(old) = allocated.referenced_stack_value {
                // TODO: I'm not entirely sure I can remove this assert, but sometimes you do want to completely override a value,
                // and then purging is fine, even if it's updated. The update is just lost.
                if old.stack_offset + old.size > stack_offset && old.stack_offset < stack_offset + size {
                    if old.updated && old.stack_offset < stack_offset || old.stack_offset + old.size > stack_offset + size {
                        todo!("Purging of things that aren't sub-values of the original, and that are updated");
                    }

                    if DEBUG_SPAM { writeln!(self.out, "; Purged {}--{}", old.stack_offset, old.stack_offset + old.size)?; }
                    allocated.referenced_stack_value = None;
                }
            }
        }

        Ok(())
    }

    /// Tells the allocator that a register was written to. This is important, because it makes sure stack values
    /// are kept track of properly. Though, `emit_dat_dat` call this internally, so those are fine.
    fn reg_written_to(&mut self, reg: Register) {
        let register = &mut self.registers.allocated[reg as u8 as usize];
        debug_assert!(register.in_use);
        if let Some(old) = register.referenced_stack_value.take() {
            debug_assert!(!old.updated, "Before writing to a register, you need to write the old value it contained");
        }
    }

    /// Forces an allocation of a specific register. Will crash if the register is currently
    /// in use.
    fn alloc_specific_reg(&mut self, reg: Register) -> Result<Register, fmt::Error> {
        let register = &mut self.registers.allocated[reg as u8 as usize];
        debug_assert!(!register.in_use);
        self.registers.usage_ctr += 1;
        register.last_usage = self.registers.usage_ctr;
        register.in_use = true;

        // TODO: In some cases this may not be needed.
        self.push_reg_changes(reg)?;

        Ok(reg)
    }

    /// Allocates a register.
    fn alloc_reg(&mut self) -> Result<Register, fmt::Error> {
        let mut best = None;
        let mut best_last_usage = u32::MAX;
        for &prev_id in AVAILABLE_REGISTERS {
            let prev_reg = &mut self.registers.allocated[prev_id as u8 as usize];
            if !prev_reg.in_use {
                if prev_reg.last_usage < best_last_usage {
                    best = Some(prev_id);
                    best_last_usage = prev_reg.last_usage;
                }
            }
        }

        let prev_id = best.expect("Out of registers to allocate!");
        if DEBUG_SPAM { writeln!(self.out, "; allocated {}", prev_id.name(8)).unwrap(); }

        let prev_reg = &mut self.registers.allocated[prev_id as u8 as usize];

        self.registers.usage_ctr += 1;
        prev_reg.last_usage = self.registers.usage_ctr;
        prev_reg.in_use = true;
        Ok(prev_id)
    }

    fn alloc_reg_with_stack_value(
        &mut self,
        value: StackValue,
        size: usize,
    ) -> Result<Option<Register>, fmt::Error> {
        let stack_offset = self.stack.get_stack_offset(&value);

        let mut existing = None;
        let mut existing_in_use = true;
        for &prev_id in AVAILABLE_REGISTERS {
            let prev_reg = &mut self.registers.allocated[prev_id as u8 as usize];

            if let Some(prev) = &mut prev_reg.referenced_stack_value {
                if prev.stack_offset == stack_offset && prev.size == size {
                    if existing.is_none() || (existing_in_use && !prev_reg.in_use) {
                        existing = Some(prev_id);
                        existing_in_use = prev_reg.in_use;
                    }
                } else if prev.updated && (prev.stack_offset + prev.size > stack_offset && stack_offset + size > prev.stack_offset) {
                    // We can't copy from the register since we're not exactly overlapping, so we have to push the changes to the stack and
                    // then read it from the stack.
                    // We don't do a `existing_is_updated` check, because there may be multiple sub-regions of the stack that are updated, and we may
                    // overlap several of them.
                    self.push_reg_changes(prev_id)?;
                }
            }
        }

        // TODO: I want heuristics to help with this
        if let Some(existing) = existing {
            if !existing_in_use {
                // self.push_reg_changes(existing);

                let register = &mut self.registers.allocated[existing as u8 as usize];

                register.in_use = true;
                return Ok(Some(existing));
            }
        }

        if let Some(existing) = existing {
            let reg = self.alloc_reg()?;
            self.push_reg_changes(reg)?;

            self.registers.allocated[reg as u8 as usize].referenced_stack_value = Some(ReferencedStackValue {
                stack_offset,
                size,
                updated: false,
            });

            writeln!(self.out, "\tmov {}, {}", reg.name(size), existing.name(size))?;

            Ok(Some(reg))
        } else {
            Ok(None)
        }
    }

    fn write_stack_value(&mut self, reg: Register, value: StackValue, size: usize) -> fmt::Result {
        self.push_reg_changes(reg)?;

        let stack_offset = self.stack.get_stack_offset(&value);
        self.purge_stack_value(stack_offset, size)?;
        self.registers.allocated[reg as u8 as usize].referenced_stack_value = Some(ReferencedStackValue {
            stack_offset,
            size,
            updated: true,
        });

        Ok(())
    }

    fn read_stack_value(&mut self, reg: Register, value: StackValue, size: usize) -> fmt::Result {
        let stack_offset = self.stack.get_stack_offset(&value);

        let mut existing = None;
        for &prev_id in AVAILABLE_REGISTERS {
            let prev_reg = &mut self.registers.allocated[prev_id as u8 as usize];

            if let Some(prev) = &mut prev_reg.referenced_stack_value {
                if prev.stack_offset == stack_offset && prev.size == size {
                    if prev_id == reg {
                        // We're already the right stack value.
                        return Ok(());
                    }

                    existing = Some(prev_id);
                } else if prev.updated && (prev.stack_offset + prev.size > stack_offset && stack_offset + size > prev.stack_offset) {
                    // We can't copy from the register since we're not exactly overlapping, so we have to push the changes to the stack and
                    // then read it from the stack.
                    // We don't do a `existing_is_updated` check, because there may be multiple sub-regions of the stack that are updated, and we may
                    // overlap several of them.
                    self.push_reg_changes(prev_id)?;
                }
            }
        }

        self.push_reg_changes(reg)?;

        self.registers.allocated[reg as u8 as usize].referenced_stack_value = Some(ReferencedStackValue {
            stack_offset,
            size,
            updated: false,
        });

        if let Some(existing) = existing {
            writeln!(self.out, "\tmov {}, {}", reg.name(size), existing.name(size))?;
        } else {
            writeln!(self.out, "\tmov {}, {} [rsp+{}]", reg.name(size), name_of_size(size), stack_offset)?;
        }

        Ok(())
    }

    fn find_stack_value(&mut self, stack_offset: usize, size: usize) -> Result<(Option<Register>, bool), fmt::Error> {
        // Try to find a register that contains the value.
        let mut existing = None;
        let mut existing_is_updated = false;
        for &prev_id in AVAILABLE_REGISTERS {
            let prev_reg = &mut self.registers.allocated[prev_id as u8 as usize];

            if let Some(prev) = &mut prev_reg.referenced_stack_value {
                if prev.stack_offset == stack_offset && prev.size == size {
                    if prev.updated {
                        debug_assert!(!existing_is_updated, "Cannot have two existing is updated");
                        existing = Some(prev_id);
                        existing_is_updated = true;
                    } else if !existing_is_updated {
                        existing = Some(prev_id);
                    }
                } else if prev.updated && (prev.stack_offset + prev.size > stack_offset && stack_offset + size > prev.stack_offset) {
                    // We can't copy from the register since we're not exactly overlapping, so we have to push the changes to the stack and
                    // then read it from the stack.
                    // We don't do a `existing_is_updated` check, because there may be multiple sub-regions of the stack that are updated, and we may
                    // overlap several of them.
                    self.push_reg_changes(prev_id)?;
                }
            }
        }

        Ok((existing, existing_is_updated))
    }
}

struct Stack {
    offset: usize,
    stack_size: usize,
}

impl Stack {
    fn get_stack_offset(&self, value: &StackValue) -> usize {
        self.variables_base() + value.0
    }
    
    fn variables_base(&self) -> usize {
        self.offset - self.stack_size
    }

    fn value_with_offset(&self, value: &StackValue, offset: usize) -> impl fmt::Display {
        let result = self.offset - self.stack_size + value.0 + offset;
        Formatter(move |f| write!(f, "[rsp+{}]", result))
    }

    fn value(&self, value: &StackValue) -> impl fmt::Display {
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

    let mut prev_line = 0;
    if is_debugging {
        let loc = routine.loc;
        writeln!(out, "%line {:0>3}+000 {}", loc.line, loc.file)?;
        prev_line = loc.line;
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
        registers: Registers::default(),
    };

    let mut function_args_offset = 0;
    for instr in &routine.instr {
        if let Instr::Call { to: (_, to_layout), pointer: _, ref args, loc: _ } | Instr::CallImm { to: (_, to_layout), function_id: _, ref args, loc: _ } = instr {
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
        if DEBUG_SPAM {
            writeln!(ctx.out, "; {:?}", instr)?;
            write!(ctx.out, "; ")?;
            for (i, &reg_id) in AVAILABLE_REGISTERS.iter().enumerate() {
                if i > 0 { write!(ctx.out, ", ")?; }

                let reg = &ctx.registers.allocated[reg_id as u8 as usize];

                write!(ctx.out, "{}", reg_id.name(8))?;
                if let Some(stack_value) = reg.referenced_stack_value {
                    write!(ctx.out, " {}--{}", stack_value.stack_offset, stack_value.stack_offset + stack_value.size)?;
                    if stack_value.updated {
                        write!(ctx.out, "!")?;
                    }
                }
            }
            writeln!(ctx.out)?;
        }

        match *instr {
            Instr::DebugLocation(loc) => {
                if is_debugging {
                    if loc.line != prev_line {
                        writeln!(ctx.out, "%line {:0>3}+000 {}", loc.line, loc.file)?;
                        prev_line = loc.line;
                    }
                }
            }
            // @Copypasta: from other call
            Instr::CallImm { to: (to, to_layout), function_id, ref args, loc: _ } => {
                // @Incomplete: We want to look at which calling convention we're using here too,
                // for now we just assume the standard x64 convention

                // TODO: Actually use the register allocator in the call emission
                ctx.flush_all()?;

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

                let routine = program.get_routine(function_id).unwrap();
                match &*routine {
                    Routine::Extern(symbol_name) => {
                        writeln!(ctx.out, "\tcall {}", symbol_name)?;
                    }
                    _ => {
                        writeln!(ctx.out, "\tcall {}", function_symbol(function_id))?;
                    }
                }

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
            Instr::Call { to: (to, to_layout), pointer, ref args, loc: _ } => {
                // @Incomplete: We want to look at which calling convention we're using here too,
                // for now we just assume the standard x64 convention

                // TODO: Actually use the register allocator in the call emission
                ctx.flush_all()?;

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
                for split in split_into_powers_of_two_with_max(size, 8) {
                    let mut number = [0_u8; 8];
                    number[..split.size].copy_from_slice(&from[split.offset..split.offset + split.size]);
                    let number = u64::from_le_bytes(number);

                    // TODO: We probably want to prefer a register that already contained the old stack value.
                    let temp = ctx.alloc_reg()?;
                    ctx.emit_write_dat("mov", temp, split.size, DataHandle::Imm(number, split.size))?;
                    ctx.write_stack_value(temp, StackValue(to.0 + split.offset), split.size)?;
                    ctx.free_all();
                }
            }
            Instr::Move { to, from, size } => {
                for split in split_into_powers_of_two(size) {
                    let from = ctx.get_data(Data::Stack(StackValue(from.0 + split.offset), split.size), READ)?;
                    let temp = ctx.alloc_reg()?;
                    ctx.emit_write_dat("mov", temp, split.size, from)?;
                    ctx.write_stack_value(temp, StackValue(to.0 + split.offset), split.size)?;
                    ctx.free_all();
                }
            }
            Instr::StackPtr { to, take_pointer_to } => {
                // TODO: This could probably be cleaned up, but for now, addresses aren't supported in the context emission.
                let temp = ctx.alloc_reg()?;
                ctx.push_reg_changes(temp)?;
                writeln!(ctx.out, "\tlea {}, {}", temp.name(8), ctx.stack.value(&take_pointer_to))?;
                ctx.reg_written_to(temp);
                ctx.write_stack_value(temp, to, 8)?;

                ctx.free_all();
            }
            Instr::IncrPtr { to, amount, scale } => {
                // TODO: Implement this
                ctx.flush_all()?;
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
                if is_debugging {
                    // This lets you see the label name for jump instructions
                    // in the debugger.
                    writeln!(extern_defs, "global {}", label_name(function_id, label_id))?;
                }

                // We don't know where one might jump in here from, so we have to loose
                // all information about registers.
                // Important that this is before the label, otherwise we'll just mess
                // up the state!
                ctx.flush_all()?;

                writeln!(ctx.out, "{}:", label_name(function_id, label_id))?;
            }
            Instr::Unary { to, from, op, type_ } => {
                assert!(!type_.is_float(), "Float operations not handled yet in x64 backend");

                let size = type_.size();
                emit_unary(&mut ctx, op, type_, to, Data::Stack(from, size), size)?;
            }
            Instr::Binary { to, a, b, op, type_ } => {
                assert!(!type_.is_float(), "Float operations not handled yet in x64 backend");

                let size = type_.size();
                emit_binary(&mut ctx, op, type_, to, Data::Stack(a, size), Data::Stack(b, size), size)?;
            }
            Instr::BinaryImm { to, a, b, op, type_ } => {
                assert!(!type_.is_float(), "Float operations not handled yet in x64 backend");

                let size = type_.size();
                emit_binary(&mut ctx, op, type_, to, Data::Stack(a, size), Data::Imm(b, size), size)?;
            }
            Instr::JumpIfZero { condition, to } => {
                // We don't know what the thing at the other end is going to want,
                // so we need to put the stack up to date.
                ctx.push_all_changes()?;

                let cond = ctx.get_data(Data::Stack(condition, 1), READ)?;
                writeln!(ctx.out, "\tcmp {}, 0", cond.print(&ctx.stack))?;
                writeln!(ctx.out, "\tje  {}", label_name(function_id, to))?;
            }
            Instr::Jump { to } => {
                // We don't know what the state is going
                // to be at the other end. The instructions
                // after this are unreachable except through a label,
                // so the state we leave the ctx in is irrelevant,
                // though I just flush all to be nice.
                ctx.flush_all()?;
                writeln!(ctx.out, "\tjmp  {}", label_name(function_id, to))?;
            }
            Instr::RefGlobal { to_ptr, global } => {
                let reg = ctx.alloc_reg()?;
                ctx.push_reg_changes(reg)?;
                writeln!(ctx.out, "\tmov {}, {}", reg.name(8), global_symbol(global.as_ptr() as usize))?;
                ctx.reg_written_to(reg);
                ctx.write_stack_value(reg, to_ptr, 8)?;
            }
            Instr::IndirectMove { to_ptr, from, offset, size } => {
                ctx.flush_all()?;

                // TODO: Think about if we can improve this somehow, but I'm not sure we can, because we don't know
                // where to is.
                writeln!(ctx.out, "\tmov rax, {}", ctx.stack.value(&to_ptr))?;

                for split in split_into_powers_of_two(size) {
                    let reg_name = Register::Rcx.name(split.size);
                    writeln!(ctx.out, "\tmov {}, {} {}", reg_name, name_of_size(split.size), ctx.stack.value_with_offset(&from, split.offset))?;
                    writeln!(ctx.out, "\tmov {} [rax+{}], {}", name_of_size(split.size), split.offset + offset, reg_name)?;
                }
            }
            Instr::Dereference { to, from_ptr, offset, size } => {
                ctx.push_all_changes()?;

                let ptr_reg = ctx.alloc_reg()?;
                ctx.reg_written_to(ptr_reg);

                writeln!(ctx.out, "\tmov {}, {}", ptr_reg.name(8), ctx.stack.value(&from_ptr))?;

                for split in split_into_powers_of_two(size) {
                    let temp_reg = ctx.alloc_reg()?;
                    ctx.push_reg_changes(temp_reg)?;
                    writeln!(ctx.out, "\tmov {}, {} [{}+{}]", temp_reg.name(split.size), name_of_size(split.size), ptr_reg.name(8), split.offset + offset)?;
                    ctx.reg_written_to(temp_reg);

                    ctx.write_stack_value(temp_reg, StackValue(to.0 + split.offset), split.size)?;
                    ctx.free_reg(temp_reg);
                }
            }
            Instr::SetToZero { to_ptr: to, size } => {
                for split in split_into_powers_of_two(size) {
                    let temp = ctx.alloc_reg()?;
                    ctx.emit_write_dat("xor", temp, split.size, DataHandle::Reg(temp, split.size))?;
                    ctx.write_stack_value(temp, StackValue(to.0 + split.offset), split.size)?;
                    ctx.free_reg(temp);
                }
            }
            Instr::ConvertNum { to, from, to_number, from_number } => {
                assert!(!to_number.is_float());
                assert!(!from_number.is_float());

                match to_number.size().cmp(&from_number.size()) {
                    Ordering::Greater => {
                        let needs_sign_extend = to_number.signed() && from_number.signed();

                        let reg = ctx.get_data_as_reg(Data::Stack(from, from_number.size()))?;

                        if needs_sign_extend {
                            ctx.emit_write_dat("movsx", reg, to_number.size(), DataHandle::Reg(reg, from_number.size()))?;
                        } else {
                            if from_number.size() == 4 {
                                // Writing to a 32 bit register is already a zero extend, which means,
                                // that `reg` is already zero extended.
                            } else {
                                ctx.emit_write_dat("movzx", reg, to_number.size(), DataHandle::Reg(reg, from_number.size()))?;
                            }
                        }

                        ctx.write_stack_value(reg, to, to_number.size())?;
                    }
                    Ordering::Equal => {
                        let reg = ctx.get_data_as_reg(Data::Stack(from, from_number.size()))?;
                        ctx.write_stack_value(reg, to, to_number.size())?;
                    }
                    Ordering::Less => {
                        let reg = ctx.get_data_as_reg(Data::Stack(from, from_number.size()))?;
                        ctx.write_stack_value(reg, to, to_number.size())?;
                    }
                }
            }
        }

        ctx.free_all();
    }

    // TODO: We can use existing values if they exist and have those help out.
    ctx.flush_all()?;

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
enum StackValueInRegister {
    Exact,
    Cropped {
        offset: usize,
        existing_size: usize,
    },
}

type AllowedDataFlags = u64;
const ALLOWED_DATA_FLAG_MAX_IMM_SIZE: AllowedDataFlags = 0b0000_1111;
const ALLOWED_DATA_FLAG_INDIRECT:     AllowedDataFlags = 0b0010_0000;

const READ: AllowedDataFlags = ALLOWED_DATA_FLAG_INDIRECT | (ALLOWED_DATA_FLAG_MAX_IMM_SIZE & 4);
const READ_NO_INDIRECT: AllowedDataFlags = ALLOWED_DATA_FLAG_MAX_IMM_SIZE & 4;
const READ_WITH_IMM64: AllowedDataFlags = ALLOWED_DATA_FLAG_INDIRECT | (ALLOWED_DATA_FLAG_MAX_IMM_SIZE & 8);
const READ_REG: AllowedDataFlags = 0;

#[derive(Clone, Copy)]
enum Data {
    Stack(StackValue, usize),
    Imm(u64, usize),
    Reg(Register, usize),
}

#[derive(Clone, Copy)]
enum DataHandle {
    Reg(Register, usize),
    Stack(StackValue, usize),
    Imm(u64, usize),
}

impl DataHandle {
    fn truncate_to_size(self, new_size: usize) -> Self {
        match self {
            Self::Reg(reg, _) => Self::Reg(reg, new_size),
            Self::Stack(val, _) => Self::Stack(val, new_size),
            Self::Imm(val, _) => Self::Imm(val, new_size),
        }
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

fn emit_unary(ctx: &mut Context<'_>, op: UnaryOp, type_: PrimitiveType, to: StackValue, a: Data, size: usize) -> fmt::Result {
    match op {
        UnaryOp::Not => {
            if matches!(type_, PrimitiveType::Bool) {
                let to_reg = ctx.alloc_reg()?;
                let a = ctx.get_data(a, READ)?;
                ctx.emit_dat_dat("cmp", a, DataHandle::Imm(0, 1))?;
                ctx.emit_write("sete", to_reg, size)?;
                ctx.write_stack_value(to_reg, to, size)?;
            } else {
                let to_reg = ctx.get_data_as_reg(a)?;
                ctx.emit_write("not", to_reg, size)?;
                ctx.write_stack_value(to_reg, to, size)?;
            }
        }
        UnaryOp::Negate => {
            let to_reg = ctx.get_data_as_reg(a)?;
            ctx.emit_write("neg", to_reg, size)?;
            ctx.write_stack_value(to_reg, to, size)?;
        }
        _ => {
            writeln!(ctx.out, "\t; Unhandled unary operator {:?}", op)?;
            println!("\t; Unhandled unary operator {:?}", op);
        }
    }

    ctx.free_all();

    Ok(())
}

fn emit_binary(ctx: &mut Context<'_>, op: BinaryOp, type_: PrimitiveType, to: StackValue, a: Data, b: Data, size: usize) -> fmt::Result {
    match op {
        BinaryOp::Add => {
            let a = ctx.get_data_as_reg(a)?;
            let b = ctx.get_data(b, READ)?;
            ctx.emit_write_dat("add", a, size, b)?;
            ctx.write_stack_value(a, to, size)?;
        }
        BinaryOp::Sub => {
            let a = ctx.get_data_as_reg(a)?;
            let b = ctx.get_data(b, READ)?;
            ctx.emit_write_dat("sub", a, size, b)?;
            ctx.write_stack_value(a, to, size)?;
        }
        BinaryOp::Mult => {
            if size > 1 {
                // This is written to for overflowing values in this case.
                // @Cleanup: Should make a `poison_reg` function that just prepares a register
                // for being filled with junk.
                ctx.alloc_specific_reg(Register::Rdx)?;
                ctx.push_reg_changes(Register::Rdx)?;
                ctx.reg_written_to(Register::Rdx);
            }

            let to_reg = ctx.alloc_specific_reg(Register::Rax)?;
            let a = ctx.get_data(a, READ)?;
            let b = ctx.get_data(b, READ_REG)?;

            ctx.emit_write_dat("mov", to_reg, size, a)?;

            if type_.signed() {
                ctx.emit_dat("imul", b)?;
            } else {
                ctx.emit_dat("mul", b)?;
            }
            ctx.write_stack_value(to_reg, to, size)?;
        }
        BinaryOp::Div => {
            if size > 1 {
                ctx.alloc_specific_reg(Register::Rdx)?;
                ctx.push_reg_changes(Register::Rdx)?;
            }

            ctx.alloc_specific_reg(Register::Rax)?;
            let a = ctx.get_data(a, READ)?;
            ctx.emit_write_dat("mov", Register::Rax, size, a)?;

            if size > 1 {
                ctx.reg_written_to(Register::Rdx);
            }

            let b = ctx.get_data(b, READ_REG)?;

            if type_.signed() {
                match size {
                    1 => writeln!(ctx.out, "\tmovsx ax, al")?,
                    2 => writeln!(ctx.out, "\tcwd")?,
                    4 => writeln!(ctx.out, "\tcdq")?,
                    8 => writeln!(ctx.out, "\tcqo")?,
                    _ => unreachable!(),
                }
                writeln!(ctx.out, "\tidiv {}", b.print(&ctx.stack))?;
            } else {
                if size == 1 {
                    writeln!(ctx.out, "\tmovzx rax, al")?;
                } else {
                    writeln!(ctx.out, "\txor {reg_name:}, {reg_name:}", reg_name = Register::Rdx.name(size))?;
                }
                writeln!(ctx.out, "\tdiv {}", b.print(&ctx.stack))?;
            }
            ctx.reg_written_to(Register::Rax);

            ctx.write_stack_value(Register::Rax, to, size)?;
        }
        BinaryOp::Modulo => {
            if size > 1 {
                ctx.alloc_specific_reg(Register::Rdx)?;
                ctx.push_reg_changes(Register::Rdx)?;
            }

            ctx.alloc_specific_reg(Register::Rax)?;
            let a = ctx.get_data(a, READ)?;
            ctx.emit_write_dat("mov", Register::Rax, size, a)?;

            if size > 1 {
                ctx.reg_written_to(Register::Rdx);
            }

            let b = ctx.get_data(b, READ_REG)?;

            if type_.signed() {
                match size {
                    1 => writeln!(ctx.out, "\tmovsx ax, al")?,
                    2 => writeln!(ctx.out, "\tcwd")?,
                    4 => writeln!(ctx.out, "\tcdq")?,
                    8 => writeln!(ctx.out, "\tcqo")?,
                    _ => unreachable!(),
                }
                writeln!(ctx.out, "\tidiv {}", b.print(&ctx.stack))?;
            } else {
                if size == 1 {
                    writeln!(ctx.out, "\tmovzx rax, al")?;
                } else {
                    writeln!(ctx.out, "\txor {reg_name:}, {reg_name:}", reg_name = Register::Rdx.name(size))?;
                }
                writeln!(ctx.out, "\tdiv {}", b.print(&ctx.stack))?;
            }
            ctx.reg_written_to(Register::Rax);

            if size > 1 {
                ctx.write_stack_value(Register::Rdx, to, size)?;
            } else {
                writeln!(ctx.out, "\tsar rax, 8")?;
                ctx.write_stack_value(Register::Rax, to, 1)?;
            }
        }
        BinaryOp::ShiftLeft => {
            // TODO: If I add a `get_data_in_reg` later, this could use that.
            let cl = ctx.alloc_specific_reg(Register::Rcx)?;
            let a = ctx.get_data_as_reg(a)?;
            let b = ctx.get_data(b, READ)?.truncate_to_size(1);

            ctx.emit_write_dat("mov", cl, 1, b)?;
            ctx.emit_write_dat("shl", a, size, DataHandle::Reg(cl, 1))?;
            ctx.write_stack_value(a, to, size)?;
        }
        BinaryOp::ShiftRight => {
            // TODO: If I add a `get_data_in_reg` later, this could use that.
            let cl = ctx.alloc_specific_reg(Register::Rcx)?;
            let a = ctx.get_data_as_reg(a)?;
            let b = ctx.get_data(b, READ)?.truncate_to_size(1);

            ctx.emit_write_dat("mov", cl, 1, b)?;
            ctx.emit_write_dat("sar", a, size, DataHandle::Reg(cl, 1))?;
            ctx.write_stack_value(a, to, size)?;
        }
        BinaryOp::Equals => {
            let out = ctx.alloc_reg()?;
            let a = ctx.get_data(a, READ)?;
            let b = ctx.get_data(b, READ_NO_INDIRECT)?;

            ctx.emit_dat_dat("cmp", a, b)?;
            ctx.emit_write("sete", out, 1)?;
            ctx.write_stack_value(out, to, 1)?;
        }
        BinaryOp::NotEquals => {
            let out = ctx.alloc_reg()?;
            let a = ctx.get_data(a, READ)?;
            let b = ctx.get_data(b, READ_NO_INDIRECT)?;

            ctx.emit_dat_dat("cmp", a, b)?;
            ctx.emit_write("setne", out, 1)?;
            ctx.write_stack_value(out, to, 1)?;
        }
        BinaryOp::LargerThan => {
            let out = ctx.alloc_reg()?;
            let a = ctx.get_data(a, READ)?;
            let b = ctx.get_data(b, READ_NO_INDIRECT)?;

            ctx.emit_dat_dat("cmp", a, b)?;
            if type_.signed() {
                ctx.emit_write("setg", out, 1)?;
            } else {
                ctx.emit_write("seta", out, 1)?;
            }
            ctx.write_stack_value(out, to, 1)?;
        }
        BinaryOp::LargerThanEquals => {
            let out = ctx.alloc_reg()?;
            let a = ctx.get_data(a, READ)?;
            let b = ctx.get_data(b, READ_NO_INDIRECT)?;

            ctx.emit_dat_dat("cmp", a, b)?;
            if type_.signed() {
                ctx.emit_write("setge", out, 1)?;
            } else {
                ctx.emit_write("setae", out, 1)?;
            }
            ctx.write_stack_value(out, to, 1)?;
        }
        BinaryOp::LessThan => {
            let out = ctx.alloc_reg()?;
            let a = ctx.get_data(a, READ)?;
            let b = ctx.get_data(b, READ_NO_INDIRECT)?;

            ctx.emit_dat_dat("cmp", a, b)?;
            if type_.signed() {
                ctx.emit_write("setl", out, 1)?;
            } else {
                ctx.emit_write("setb", out, 1)?;
            }
            ctx.write_stack_value(out, to, 1)?;
        }
        BinaryOp::LessThanEquals => {
            let out = ctx.alloc_reg()?;
            let a = ctx.get_data(a, READ)?;
            let b = ctx.get_data(b, READ_NO_INDIRECT)?;

            ctx.emit_dat_dat("cmp", a, b)?;
            if type_.signed() {
                ctx.emit_write("setle", out, 1)?;
            } else {
                ctx.emit_write("setbe", out, 1)?;
            }
            ctx.write_stack_value(out, to, 1)?;
        }
        BinaryOp::And | BinaryOp::BitAnd => {
            let a = ctx.get_data_as_reg(a)?;
            let b = ctx.get_data(b, READ)?;
            ctx.emit_write_dat("and", a, size, b)?;
            ctx.write_stack_value(a, to, size)?;
        }
        BinaryOp::Or | BinaryOp::BitOr => {
            let a = ctx.get_data_as_reg(a)?;
            let b = ctx.get_data(b, READ)?;
            ctx.emit_write_dat("or", a, size, b)?;
            ctx.write_stack_value(a, to, size)?;
        }
        _ => {
            writeln!(ctx.out, "\t; Unhandled binary operator {:?}", op)?;
            println!("\t; Unhandled binary operator {:?}", op);
        }
    }

    ctx.free_all();

    Ok(())
}
