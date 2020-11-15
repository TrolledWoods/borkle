#![deny(rust_2018_idioms, clippy::pedantic, clippy::all)]
#![feature(bool_to_option)]

mod errors;
mod literal;
mod locals;
mod location;
mod operators;
mod parser;

fn main() {
    let mut errors = errors::ErrorCtx::new();
    let result = parser::process_string(
        &mut errors,
        "hi".into(),
        r#"
        {
            1 + 2 * 4;
        }
    "#,
    );

    if let Ok(ast) = result {
        println!("{:#?}", ast);
    }
    errors.print();
}
