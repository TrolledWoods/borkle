use std::path::PathBuf;
use crate::program::{Program, FunctionId};
use crate::ir::Routine;
use std::fmt;

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

                    let entry_point = program.get_entry_point().unwrap();

                    let mut command = std::process::Command::new("nasm");
                    command.arg(&path);
                    if program.arguments.debug_asm_output {
                        command.arg("--no-line");
                    }
                    command.arg("-fwin64");
                    command.arg("-g");
                    command.arg("-Fcv8");
                    command.stdout(std::process::Stdio::inherit());
                    command.stderr(std::process::Stdio::inherit());

                    println!("nasm command: {:?}", command);

                    match command.output() {
                        Ok(output) => {
                            use std::io::Write;
                            std::io::stdout().write_all(&output.stdout).unwrap();
                            std::io::stderr().write_all(&output.stderr).unwrap();
                        }
                        Err(err) => println!("Failed to run nasm: {:?}", err),
                    }

                    let mut path = path.to_path_buf();
                    path.set_extension("obj");

                    // @Improvement: Use vswhere instead, right now just run `cargo run` in the Native Tools
                    // command prompt.
                    let mut command = std::process::Command::new("cl");
                    command.arg(&path);
                    command.arg("/Fetarget\\output.exe");
                    command.arg("/Zi");
                    command.arg("/link");
                    command.arg("/release");
                    command.arg("/incremental:no");
                    command.arg("OneCore.lib");
                    command.arg("/debug");
                    command.arg("/subsystem:console");
                    command.arg(format!("/entry:function_{}", usize::from(entry_point)));

                    command.stdout(std::process::Stdio::inherit());
                    command.stderr(std::process::Stdio::inherit());

                    println!("cl command: {:?}", command);

                    match command.output() {
                        Ok(output) => {
                            use std::io::Write;
                            std::io::stdout().write_all(&output.stdout).unwrap();
                            std::io::stderr().write_all(&output.stderr).unwrap();
                        }
                        Err(err) => println!("Failed to link: {:?}", err),
                    }
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
    ) {
        for emitter in &mut self.emitters { 
            match emitter {
                BackendEmitter::C { .. } => {
                    // v.emit_routine(program, id, routine, arg_types, return_type);
                }
                BackendEmitter::Ir(v) => {
                    v.emit_routine(program, id, routine);
                }
                BackendEmitter::X64(v) => {
                    v.emit_routine(program, id, routine);
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

struct Formatter<F>(F)
where
    F: for<'a> Fn(&mut fmt::Formatter<'a>) -> fmt::Result;

impl<F> fmt::Display for Formatter<F>
where
    F: for<'a> Fn(&mut fmt::Formatter<'a>) -> fmt::Result,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.0)(f)
    }
}

pub fn function_symbol(function: FunctionId) -> impl fmt::Display {
    let num: usize = function.into();
    Formatter(move |f| write!(f, "function_{}", num))
}

pub fn global_symbol(global: usize) -> impl fmt::Display {
    Formatter(move |f| write!(f, "global_{}", global))
}
