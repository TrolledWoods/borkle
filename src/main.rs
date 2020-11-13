#![deny(rust_2018_idioms, clippy::pedantic, clippy::all)]
mod lexer;

fn main() {
    println!("Size of Token: {}", std::mem::size_of::<lexer::Token>());
    for token in lexer::process_string(
        "NO FILE HERE".into(),
        "Hello world this 42 14299 

        is just +-* /= some if const identifiers",
    ) {
        println!("{:?}", token);
    }
}
