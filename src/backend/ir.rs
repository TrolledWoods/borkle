use crate::ir::{Instr, UserDefinedRoutine, Routine};
use crate::program::{Program, FunctionId};
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
        program: &Program,
        function_id: FunctionId,
        routine: &Routine,
    ) {
        if let Routine::UserDefined(routine) = routine {
            print_instr_list(&mut self.text, program, function_id, routine);
        }
    }
}

pub fn emit(program: &Program, file_path: &Path) {
    use std::io::Write;

    let Ok(mut file) = std::fs::File::create(file_path) else {
        println!("Failed to create output file {}", file_path.display());
        return;
    };

    // TODO: This should be cleaned up, old system
    let mut emitter = Emitter::default();
    let routines = program.get_routines();
    for (id, routine) in routines.iter() {
        emitter.emit_routine(program, id, routine);
    }
    drop(routines);
    if let Err(_) = write!(&mut file, "{}", emitter.text) {
        println!("Failed to write ir to output file, {}", file_path.display());
    }
}

fn print_instr_list(out: &mut String, program: &Program, function_id: FunctionId, routine: &UserDefinedRoutine) {
    writeln!(out, "\nfn {}: ({})", routine.name, usize::from(function_id)).unwrap();
    for instr in &routine.instr {
        print_instr(&mut *out, program, instr);
    }
}

pub fn print_instr(mut out: impl Write, program: &Program, instr: &Instr) {
    match instr {
        Instr::DebugLocation(loc) => {
            writeln!(out, "# {}, {}", loc.line, loc.file).unwrap();
        },
        Instr::CallImm { to, function_id, args, loc: _ } => {
            let routine = program.get_routine(*function_id).unwrap();
            let name = match &*routine {
                Routine::UserDefined(routine) => routine.name,
                Routine::Extern(name) => *name,
                Routine::Builtin(thing) => format!("{:?}", thing).into(),
            };

            write!(out, "\tcall {}, {} ({}), (", to.0, name, usize::from(*function_id)).unwrap();

            for (i, &(arg, _)) in args.iter().enumerate() {
                if i > 0 { write!(out, ", ").unwrap(); }
                write!(out, "{}", arg).unwrap();
            }

            writeln!(out, ")").unwrap();
        }
        Instr::Call { to, pointer, args, loc: _ } => {
            write!(out, "\tcall {}, {}, (", to.0, pointer).unwrap();

            for (i, &(arg, _)) in args.iter().enumerate() {
                if i > 0 { write!(out, ", ").unwrap(); }
                write!(out, "{}", arg).unwrap();
            }

            writeln!(out, ")").unwrap();
        }
        Instr::TargetBlock { target, to } => {
            writeln!(out, "target {:X}, else {}", target, to).unwrap();
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
        Instr::Dereference { to, from_ptr, offset, size } => {
            if *offset == 0 {
                writeln!(out, "\tderef {}, {} /{}", to, from_ptr, size).unwrap();
            } else {
                writeln!(out, "\tderef {}, {} + {} /{}", to, from_ptr, offset, size).unwrap();
            }
        }
        Instr::IndirectMove { to_ptr, from, offset, size } => {
            if *offset == 0 {
                writeln!(out, "\tmove_indirect {}, {} /{}", to_ptr, from, size).unwrap();
            } else {
                writeln!(out, "\tmove_indirect {} + {}, {} /{}", to_ptr, offset, from, size).unwrap();
            }
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
