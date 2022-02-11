use std::path::Path;
use crate::program::{Program, FunctionId};
use std::fmt;

// mod c;
pub mod ir;
mod x64;

pub fn emit_bir(program: &Program, path: &Path) {
    ir::emit(program, &path);
}

pub fn emit_x64(program: &Program, path: &Path, entry_point: FunctionId) {
    let mut asm_path = path.to_path_buf();
    asm_path.set_extension("asm");

    x64::emit(program, &asm_path);

    let mut command = std::process::Command::new("nasm");
    command.arg(&asm_path);
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

    let mut obj_path = path.to_path_buf();
    obj_path.set_extension("obj");

    // @Improvement: Use vswhere instead, right now just run `cargo run` in the Native Tools
    // command prompt.
    let mut command = std::process::Command::new("cl");
    command.arg(&obj_path);
    command.arg(format!("/Fe{}", path.display()));
    command.arg("/Zi");
    command.arg("/nologo");
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
        Ok(_) => {}
        Err(err) => println!("Failed to link: {:?}", err),
    }
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
