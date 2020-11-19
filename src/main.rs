#![deny(rust_2018_idioms, clippy::pedantic, clippy::all)]
#![warn(clippy::nursery)]
#![allow(clippy::module_name_repetitions, clippy::too_many_lines)]
#![feature(bool_to_option)]

mod dependencies;
mod errors;
mod literal;
mod locals;
mod location;
mod operators;
mod parser;
mod program;

fn main() {
    let mut errors = errors::ErrorCtx::new();
    let mut program = program::Program::new();
    let _ = parser::process_string(
        &mut errors,
        &program,
        "testing.bo".into(),
        &std::fs::read_to_string("testing.bo").unwrap(),
    );

    errors.print();
}
