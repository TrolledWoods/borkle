use std::path::PathBuf;
use crate::program::{Program, FunctionId};
use crate::ir::Routine;
use crate::types::Type;

// mod c;
pub mod ir;
mod x64;

#[derive(Default)]
pub struct Backends {
    pub backends: Vec<Backend>,
}

impl Backends {
    pub fn create_emitters(&self) -> BackendEmitters {
        let emitters = self.backends.iter().map(|v| {
            match v {
                Backend::C { .. } => BackendEmitter::C, // (c::Emitter::default()),
                Backend::Ir { .. } => BackendEmitter::Ir(Default::default()),
                Backend::X64 { .. } => BackendEmitter::X64(Default::default()),
            }
        }).collect();

        BackendEmitters {
            emitters
        }
    }

    pub fn emit(self, program: &Program, mut emitters: Vec<BackendEmitters>) {
        for backend in self.backends.into_iter().rev() {
            match backend {
                Backend::C { path: _, compile_output: _ } => {
                    todo!()
                    /*let c_emitters = emitters.iter_mut()
                        .map(|v| v.emitters.pop())
                        .map(|v| match v {
                            Some(BackendEmitter::C(emitter)) => emitter,
                            _ => unreachable!(),
                        })
                        .collect();
                    c::emit(program, &path, c_emitters);

                    if compile_output {
                        let mut command = std::process::Command::new(&program.arguments.c_compiler);
                        command.arg(&path);
                        command.arg("-o");
                        command.arg(&program.arguments.exe_path);
                        // command.arg("-O3");
                        command.arg("-g");
                        command.arg("-O0");
                        command.arg("-Wno-everything");

                        command.stdout(std::process::Stdio::inherit());
                        command.stderr(std::process::Stdio::inherit());

                        println!("Compilation command: {:?}", command);

                        match command.output() {
                            Ok(output) => {
                                use std::io::Write;
                                std::io::stdout().write_all(&output.stdout).unwrap();
                                std::io::stderr().write_all(&output.stderr).unwrap();
                            }
                            Err(err) => println!("Failed to run c compiler: {:?}", err),
                        }
                    }*/
                }
                Backend::Ir { path } => {
                    let ir_emitters = emitters.iter_mut()
                        .map(|v| v.emitters.pop())
                        .map(|v| match v {
                            Some(BackendEmitter::Ir(emitter)) => emitter,
                            _ => unreachable!(),
                        })
                        .collect();
                    ir::emit(program, &path, ir_emitters);
                }
                Backend::X64 { path } => {
                    let ir_emitters = emitters.iter_mut()
                        .map(|v| v.emitters.pop())
                        .map(|v| match v {
                            Some(BackendEmitter::X64(emitter)) => emitter,
                            _ => unreachable!(),
                        })
                        .collect();
                    x64::emit(program, &path, ir_emitters);
                }
            }
        }
    }
}

pub enum Backend {
    C {
        path: PathBuf,
        compile_output: bool,
    },
    Ir {
        path: PathBuf,
    },
    X64 {
        path: PathBuf,
    },
}

pub struct BackendEmitters {
    emitters: Vec<BackendEmitter>,
}

impl BackendEmitters {
    pub fn emit_routine(
        &mut self, 
        program: &Program,
        id: FunctionId,
        routine: &Routine,
        arg_types: &[Type],
        return_type: Type,
    ) {
        for emitter in &mut self.emitters { 
            match emitter {
                BackendEmitter::C { .. } => {
                    // v.emit_routine(program, id, routine, arg_types, return_type);
                }
                BackendEmitter::Ir(v) => {
                    v.emit_routine(program, id, routine, arg_types, return_type);
                }
                BackendEmitter::X64(v) => {
                    v.emit_routine(program, id, routine, arg_types, return_type);
                }
            }
        }
    }
}

enum BackendEmitter {
    C, // (c::Emitter),
    X64(x64::Emitter),
    Ir(ir::Emitter),
}

