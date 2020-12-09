#![deny(rust_2018_idioms, clippy::all)]

mod c_backend;
mod command_line_arguments;
mod dependencies;
mod errors;
mod interp;
mod ir;
mod literal;
mod locals;
mod location;
mod logging;
mod operators;
mod parser;
mod program;
mod typer;
mod types;

pub const MAX_FUNCTION_ARGUMENTS: usize = 32;

fn main() {
    let time = std::time::Instant::now();
    let logger = logging::Logger::new();

    let args: Vec<_> = std::env::args().skip(1).collect();
    let borrowed_args: Vec<&str> = args.iter().map(|v| &**v).collect();
    if let Some(options) = command_line_arguments::Arguments::from_args(&borrowed_args) {
        let num_threads = options.num_threads;
        let file = (&options.file).into();
        let output_c = options.release;
        let output_folder: std::path::PathBuf = options.output.as_str().into();

        let mut thread_pool = program::thread_pool::ThreadPool::new(
            options,
            logger,
            std::iter::once(program::Task::Parse(file)),
        );

        for _ in 1..num_threads {
            thread_pool.spawn_thread();
        }

        let program = thread_pool.program();
        // FIXME: We should make a more proper system to handle c outputting
        let (mut c_output, errors) = thread_pool.join();

        errors.print();

        // FIXME: Make a proper error message for when the entry point doesn't exist.
        let entry_point = program
            .get_entry_point()
            .expect("Entry point 'main' of program has to exist and be of type 'fn () -> u64'");

        if output_c {
            let mut c_file = output_folder;
            c_file.push("output.c");
            c_backend::entry_point(&mut c_output, entry_point);
            std::fs::write(&c_file, c_output).unwrap();
        } else {
            let mut stack = interp::Stack::new(1 << 16);
            let result = interp::interp(&program, &mut stack, unsafe {
                &*entry_point.cast::<ir::Routine>()
            });

            println!("[main returned: {}]", unsafe { *(result as *const u64) });
        }

        let elapsed = time.elapsed();
        println!("Finished in {:.4} seconds", elapsed.as_secs_f32());
    }
}
