#![deny(rust_2018_idioms, clippy::all)]

mod dependencies;
mod errors;
mod interp;
mod ir;
mod literal;
mod locals;
mod location;
mod operators;
mod parser;
mod program;
mod typer;
mod types;

pub const MAX_FUNCTION_ARGUMENTS: usize = 32;

fn main() {
    let mut thread_pool = program::thread_pool::ThreadPool::new(std::iter::once(
        program::Task::Parse("testing".into(), "testing.bo".into()),
    ));

    let time = std::time::Instant::now();

    for _ in 0..2 {
        thread_pool.spawn_thread();
    }

    let errors = thread_pool.join();

    errors.print();

    let elapsed = time.elapsed();
    println!("Finished in {:.4} seconds", elapsed.as_secs_f32());
}
