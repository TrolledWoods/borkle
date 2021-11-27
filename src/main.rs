#![feature(let_else)]
// Deny the things that are more important, since often times when refactoring code old code gets a lot of warnings for a
// long time, but I still want some of the benefits of the very useful warnings.
#![deny(rust_2018_idioms, mutable_borrow_reservation_conflict, unused_variables, unused_mut, unused_unsafe)]

mod c_backend;
mod command_line_arguments;
mod dependencies;
mod execution_time;
mod emit;
mod errors;
mod id;
mod interp;
mod ir;
mod literal;
mod locals;
mod location;
mod logging;
mod operators;
mod parser;
mod program;
mod random;
mod thread_pool;
mod type_infer;
mod typer;
mod types;

fn main() {
    profile::begin();

    let time = std::time::Instant::now();
    let logger = logging::Logger::new();

    let args: Vec<_> = std::env::args().skip(1).collect();
    let borrowed_args: Vec<&str> = args.iter().map(|v| &**v).collect();
    if let Some(options) = command_line_arguments::Arguments::from_args(&borrowed_args) {
        if options.num_threads == 0 {
            println!("Has to have at least one thread");
            return;
        }

        let mut program = program::Program::new(logger, options.clone());
        program.add_file(
            &options
                .file
                .canonicalize()
                .expect("The main source file couldn't be canonicalized"),
        );

        let (mut c_output, mut errors) = thread_pool::run(&mut program, options.num_threads);

        let files = program.file_contents();
        if !errors.print(files) {
            // There were errors!
            return;
        }

        if !options.check {
            let entry_point = match program.get_entry_point() {
                Some(value) => value,
                None => {
                    println!("Expected '#entry' to denote an entry point, and for that entry point to be of type 'fn() -> u64'");
                    return;
                }
            };

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

                let elapsed = time.elapsed();
                println!("Finished in {:.4} seconds", elapsed.as_secs_f32());
            } else {
                let elapsed = time.elapsed();
                println!(
                    "Compilation finished in {:.4} seconds",
                    elapsed.as_secs_f32()
                );

                let routine = program.get_routine(entry_point).unwrap();
                if let ir::Routine::UserDefined(routine) = &*routine {
                    let mut stack = interp::Stack::new(1 << 16);

                    // @Improvement: We want to put the entry point in here.
                    match interp::interp(&program, &mut stack, routine, &mut vec![]) {
                        Ok(result) => println!("[main returned: {}]", unsafe { result.read::<u64>() }),
                        Err(call_stack) => {
                            errors.clear();
                            for &caller in call_stack.iter().rev().skip(1) {
                                errors.info(caller, "".to_string());
                            }

                            errors.error(*call_stack.last().unwrap(), "Assert failed!".to_string());
                            let files = program.file_contents();
                            errors.print(files);
                        }
                    }
                } else {
                    println!("ERROR: For now, the entry point cannot be a built in function");
                }
            }
        } else {
            let elapsed = time.elapsed();
            println!("Finished in {:.4} seconds", elapsed.as_secs_f32());
        }
    }

    profile::finish("target\\profile_output.json");
}
