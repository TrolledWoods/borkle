#![deny(rust_2018_idioms, clippy::all)]
#![deny(mutable_borrow_reservation_conflict)]
#![warn(clippy::pedantic)]
#![allow(
    clippy::if_not_else,
    clippy::module_name_repetitions,
    clippy::single_match_else,
    clippy::match_same_arms,
    clippy::too_many_lines,
    // Closures are not supposed to have side effects!!!! Yet clippy still recommends this for
    // imperative style code with side effects. Garbage!
    clippy::option_if_let_else,
    clippy::map_err_ignore,
    // TODO: We should remove this eventually, because it is in fact kinda ugly to cast from *const
    // u8 to other types all over the place, but for now this is necessary because *const u8 is
    // used to represent arbitrary pointers.
    clippy::cast_ptr_alignment,
)]

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
        let mut thread_pool = program::thread_pool::ThreadPool::new(
            Box::new(options.clone()),
            logger,
            std::iter::once(program::Task::Parse(options.file)),
        );

        for _ in 1..options.num_threads {
            thread_pool.spawn_thread();
        }

        let program = thread_pool.program();
        // FIXME: We should make a more proper system to handle c outputting
        let (mut c_output, errors) = thread_pool.join();

        errors.print();

        if !options.check {
            // FIXME: Make a proper error message for when the entry point doesn't exist.
            let entry_point = program
                .get_entry_point()
                .expect("Entry point 'main' of program has to exist and be of type 'fn () -> u64'");

            if options.release {
                let mut c_file = options.output.clone();
                c_file.push("output.c");

                let mut exe_file = options.output.clone();
                exe_file.push("output");
                exe_file.set_extension(std::env::consts::EXE_EXTENSION);

                c_backend::entry_point(&mut c_output, entry_point);
                std::fs::write(&c_file, c_output).unwrap();

                let mut command = std::process::Command::new(&options.c_compiler);
                command.arg(&c_file);
                command.arg("-o");
                command.arg(&exe_file);
                command.arg("-O3");
                command.arg("-Wno-everything");

                for lib in program.libraries.lock().iter() {
                    let from: &std::path::Path = lib.as_str().as_ref();
                    let mut from_dll = from.to_path_buf();
                    from_dll.set_extension(std::env::consts::DLL_EXTENSION);
                    let mut to = options.output.clone();
                    to.push(from.file_name().expect(
                        "TODO: Make proper error message for lib path not having a file name",
                    ));
                    to.set_extension(std::env::consts::DLL_EXTENSION);

                    if from_dll != to {
                        println!("Copying library file {:?} to {:?}", from_dll, to);
                        std::fs::copy(&from_dll, &to).expect(
                            "TODO: Make an error message for failing to copy a dynamic library",
                        );
                    }

                    command.arg("-l");
                    command.arg(lib.as_str());
                }

                command.stdout(std::process::Stdio::inherit());
                command.stderr(std::process::Stdio::inherit());

                println!("Compilation command: {:?}", command);

                match command.output() {
                    Ok(output) => {
                        use std::io::Write;
                        std::io::stdout().write_all(&output.stdout).unwrap();
                        std::io::stderr().write_all(&output.stderr).unwrap();
                    }
                    Err(err) => println!("Failed to run c compiler: {:?}", err),
                }
            } else {
                let mut stack = interp::Stack::new(1 << 16);
                let result = interp::interp(&program, &mut stack, unsafe {
                    &*entry_point.cast::<ir::Routine>()
                });

                println!("[main returned: {}]", unsafe { *(result as *const u64) });
            }
        }

        let elapsed = time.elapsed();
        println!("Finished in {:.4} seconds", elapsed.as_secs_f32());
    }
}
