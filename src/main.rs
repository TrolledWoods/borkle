#![deny(rust_2018_idioms, clippy::pedantic, clippy::all)]
#![feature(bool_to_option)]

mod compile_units;
mod errors;
// mod global_scope;
mod literal;
mod locals;
mod location;
mod operators;
mod parser;

fn main() {
    let mut errors = errors::ErrorCtx::new();
    let compiler = compile_units::CompileUnits::new();
    compiler.add_file("testing.bo".into());

    while let Ok(true) = compiler.bump(&mut errors) {}

    errors.print();
}
