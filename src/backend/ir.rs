use crate::ir::{Instr, UserDefinedRoutine, Routine};
use crate::program::{Program, FunctionId};
use crate::types::Type;
use crate::operators::Operator;
use std::path::Path;
use std::fmt::Write;

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
            writeln!(&mut self.text, "\n\nfunction_{}:", usize::from(function_id)).unwrap();
            print_instr_list(&mut self.text, routine);
        }
    }
}

pub fn emit(program: &Program, file_path: &Path, emitters: Vec<Emitter>) {
    use std::io::Write;

    let Ok(mut file) = std::fs::File::create(file_path) else {
        println!("Failed to create output file {}", file_path.display());
        return;
    };

    let entry_id = program.get_entry_point().unwrap();
    let _ = writeln!(&mut file, "entry: function_{}", usize::from(entry_id)).unwrap();

    for emitter in &emitters {
        if let Err(_) = write!(&mut file, "{}", emitter.text) {
            println!("Failed to write ir to output file, {}", file_path.display());
        }
    }
}

fn print_instr_list(out: &mut String, routine: &UserDefinedRoutine) {
    for instr in &routine.instr {
        match instr {
            Instr::DebugLocation(_) => {},
            Instr::Call { to, pointer, args, loc: _ } => {
                write!(out, "\tcall {}, {}, (", to.0, pointer).unwrap();

                for (i, &(arg, _)) in args.iter().enumerate() {
                    if i > 0 { out.push_str(", "); }
                    write!(out, "{}", arg).unwrap();
                }

                writeln!(out, ")").unwrap();
            }
            Instr::SetToZero { to_ptr, size } => {
                writeln!(out, "\tzero {} /{}", to_ptr, size).unwrap();
            }
            Instr::Binary { to, a, b, op, type_ } => {
                writeln!(out, "\t{} = {} {} {} /{:?}", to, a, op.to_string(), b, type_).unwrap();
            }
            Instr::BinaryImm { to, a, b, op, type_ } => {
                writeln!(out, "\t{} = {} {} {} /{:?}", to, a, op.to_string(), b, type_).unwrap();
            }
            Instr::IncrPtr { to, amount, scale } => {
                writeln!(out, "\t{} += {} * {} /ptr", to, amount, scale).unwrap();
            }
            Instr::Unary { to, from, op, type_ } => {
                writeln!(out, "\t{} = {} {} /{:?}", to, op.to_string(), from, type_).unwrap();
            }
            Instr::RefGlobal { to_ptr, global } => {
                writeln!(out, "\tref_global {}, {:p}", to_ptr, global.as_ptr()).unwrap();
            }
            Instr::StackPtr { to, take_pointer_to } => {
                writeln!(out, "\tref_stack {}, {}", to, take_pointer_to).unwrap();
            }
            Instr::Move { to, from, size } => {
                writeln!(out, "\tmove {}, {} /{}", to, from, size).unwrap();
            }
            Instr::MoveImm { to, from, size } => {
                writeln!(out, "\tmove {}, {:?} /{}", to, &from[..*size], size).unwrap();
            }
            Instr::Dereference { to, from_ptr, size } => {
                writeln!(out, "\tderef {}, {} /{}", to, from_ptr, size).unwrap();
            }
            Instr::IndirectMove { to_ptr, from, size } => {
                writeln!(out, "\tmove_indirect {}, {} /{}", to_ptr, from, size).unwrap();
            }
            Instr::ConvertNum { to, from, to_number, from_number } => {
                writeln!(out, "\tconvert {}({:?}), {}({:?})", to, to_number, from, from_number).unwrap();
            }
            Instr::JumpIfZero { condition, to } => {
                writeln!(out, "\tjez {}, {}", condition, to).unwrap();
            }
            Instr::Jump { to } => {
                writeln!(out, "\tjmp {}", to).unwrap();
            }
            Instr::LabelDefinition(label) => {
                writeln!(out, "{}:", label).unwrap();
            }
        }
    }
}
