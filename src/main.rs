#![deny(rust_2018_idioms, clippy::pedantic, clippy::all)]
#![feature(bool_to_option)]

mod errors;
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
            let x = 3;
            let yes = 5;
            defer x.x.hi.super->yes;
            defer x.hello.hi.super->yes;
        }
    "#,
    );

    if let Ok(ast) = result {
        println!("{:#?}", ast);
    } else {
        errors.print();
    }
}
