use crate::ir::{Instr, UserDefinedRoutine, Routine};
use crate::layout::{align_to, Layout};
use crate::program::{Program, FunctionId};
use crate::types::Type;
use crate::operators::Operator;
use ustr::Ustr;
use std::path::Path;
use std::fmt::{self, Write};

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

    write!(&mut out, "\tglobal ").unwrap();
    let entry = program.get_entry_point().unwrap();
    write_function_name(&mut out, entry).unwrap();
    writeln!(&mut out).unwrap();

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

pub fn emit_constants(_output: &mut String, _program: &Program) {
    /* let constant_data = program.constant_data();
    for constant in constant_data.iter() {
        let ptr = constant.ptr.as_ptr();
        if constant.type_.pointers().is_empty() {
            write!(
                output,
                "const uint64_t {}[{}] = {{",
                c_format_global(ptr as usize),
                (constant.type_.size() + 7) / 8,
            )
            .unwrap();
        } else {
            write!(
                output,
                "const struct {} {} = {{",
                c_format_global_temp_type(ptr as usize),
                c_format_global(ptr as usize),
            )
            .unwrap();
        }

        let mut pointers = constant.type_.pointers().iter().peekable();
        for i in (0..constant.type_.size()).step_by(8) {
            match pointers.peek() {
                Some(&(offset, pointer_kind)) if *offset == i => {
                    let ptr_num = unsafe { *ptr.add(i).cast::<usize>() };
                    if let PointerInType::Function { .. } = pointer_kind {
                        write!(output, "&{}", c_format_function(ptr_num.into())).unwrap();
                    } else if ptr_num == 0 {
                        output.push_str("NULL");
                    } else {
                        write!(output, "&{}", c_format_global(ptr_num)).unwrap();
                    }
                    pointers.next();
                }
                _ => {
                    write!(output, "{}", unsafe { *ptr.add(i).cast::<u64>() }).unwrap();
                }
            }

            output.push_str(", ");
        }
        write!(output, "}};\n").unwrap();
    }
    */
}

fn write_function_name(out: &mut String, function_id: FunctionId) -> fmt::Result {
    write!(out, "fn_{}", usize::from(function_id))
}

fn name_of_size(layout: Layout) -> &'static str {
    match layout.size {
        1 => "BYTE",
        2 => "WORD",
        4 => "DWORD",
        8 => "QWORD",
        _ => unreachable!("This size has no name"),
    }
}

fn emit_routine(
    out: &mut String,
    function_id: FunctionId,
    routine: &UserDefinedRoutine,
) -> fmt::Result {
    writeln!(out, "; {}", routine.name)?;
    write_function_name(out, function_id)?;
    writeln!(out, ":")?;

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

                writeln!(out, "\tmov {} [rsp+{}], rax", name_of_size(to_layout), to.0 + extra_stack_space)?;

                writeln!(out, "\tadd rsp, {}", extra_stack_space)?;
            }
            _ => writeln!(out, "\t; -- Unhandled")?,
        }
    }

    writeln!(out, "\tadd rsp, {}", stack_ptr_offset)?;
    writeln!(out, "\tret")?;

    Ok(())
}
