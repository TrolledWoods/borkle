#![deny(rust_2018_idioms, clippy::pedantic, clippy::all)]
mod errors;
mod lexer;
mod location;
mod parser;
mod tree;

fn main() {
    use std::rc::Rc;
    use tree::Tree;

    let my_rc = Rc::new(42);
    let mut tree = Tree::new();
    {
        let mut node = tree.builder();
        node.set(Rc::clone(&my_rc));
        {
            let mut node = node.arg_with(Rc::clone(&my_rc));
            node.arg_with(Rc::clone(&my_rc));
            node.arg_with(Rc::clone(&my_rc));
            node.arg_with(Rc::clone(&my_rc));
        }
        node.arg_with(Rc::clone(&my_rc));
    }
    tree.set_root();
    println!("{:#?}", tree.root().unwrap());
    std::mem::drop(tree);
    assert!(Rc::try_unwrap(my_rc).is_ok());

    let mut errors = errors::ErrorCtx::new();
    let result = lexer::process_string(&mut errors, "NO".into(), "oh \"hi mark\"");

    println!("{:?}", result);
}
