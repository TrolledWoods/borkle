#![deny(rust_2018_idioms, clippy::pedantic, clippy::all)]
#![allow(
    clippy::module_name_repetitions,
    clippy::too_many_lines,
    clippy::option_if_let_else
)]

mod dependencies;
mod errors;
mod ir;
mod literal;
mod locals;
mod location;
mod operators;
mod parser;
mod program;
mod thread_pool;
mod typer;
mod types;

fn main() {
    let mut thread_pool = thread_pool::ThreadPool::new(std::iter::once(program::Task::Parse(
        "testing".into(),
        "testing.bo".into(),
    )));

    for _ in 0..2 {
        thread_pool.spawn_thread();
    }

    let errors = thread_pool.join();

    errors.print();
}
