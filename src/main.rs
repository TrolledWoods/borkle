#![deny(rust_2018_idioms, clippy::pedantic, clippy::all)]
#![warn(clippy::nursery)]
#![allow(clippy::module_name_repetitions)]
#![feature(bool_to_option)]

mod errors;
mod literal;
mod locals;
mod location;
mod operators;
mod parser;

fn main() {
    let mut errors = errors::ErrorCtx::new();
    let _ = parser::process_string(
        &mut errors,
        "testing.bo".into(),
        &std::fs::read_to_string("testing.bo").unwrap(),
    );

    errors.print();
}
