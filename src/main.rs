#![deny(rust_2018_idioms, clippy::pedantic, clippy::all)]
#![feature(bool_to_option)]

mod errors;
mod locals;
mod location;
mod parser;
mod tree;

fn main() {
    let mut errors = errors::ErrorCtx::new();
    let result = parser::process_string(
        &mut errors,
        "hi".into(),
        r#"
        {
            let x = 5;
            let y = 2;
            x;
            y;
            y;
            defer {
                2;
                6;
            };
            5;
            defer 3;
            6;
        }
    "#,
    );

    if let Ok(ast) = result {
        println!("{:#?}", ast);
    } else {
        errors.print();
    }
}
