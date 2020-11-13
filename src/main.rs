#![deny(rust_2018_idioms, clippy::all)]

mod errors;
mod lexer;
mod location;

fn main() {
    let mut errors = errors::ErrorCtx::new();
    let _ = lexer::process_string(&mut errors, "NO".into(), "oh \"hi mark");
}
