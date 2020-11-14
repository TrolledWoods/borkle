#![deny(rust_2018_idioms, clippy::pedantic, clippy::all)]
mod errors;
mod lexer;
mod location;
mod parser;
mod tree;

fn main() {
    use tree::Tree;

    let mut tree = Tree::new();
    let mut node = tree.builder();
    node.set("hi");
    {
        let mut node = node.arg_with("yes");
        node.arg_with("please");
    }
    node.arg_with("bye");
    std::mem::drop(node);

    let mut errors = errors::ErrorCtx::new();
    let result = lexer::process_string(&mut errors, "NO".into(), "oh \"hi mark\"");

    println!("{:?}", result);
}
