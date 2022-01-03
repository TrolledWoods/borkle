#![feature(let_else)]
#![feature(generic_associated_types)]
#![deny(rust_2018_idioms, mutable_borrow_reservation_conflict, unused_variables, unused_mut, unused_unsafe)]

mod layout;
mod ast;
mod backend;
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

        let mut backends = Vec::new();
        if options.output_c {
            backends.push(backend::Backend::C {
                path: options.c_path.clone(),
                compile_output: options.compile_c,
            });
        }

        if options.output_ir {
            backends.push(backend::Backend::Ir {
                path: options.ir_path.clone(),
            });
        }

        let mut program = program::Program::new(logger, options.clone(), backend::Backends { backends });
        program.add_file(
            &options
                .file
                .canonicalize()
                .expect("The main source file couldn't be canonicalized"),
        );

        let (backend_emitters, mut errors) = thread_pool::run(&mut program, options.num_threads);

        let files = program.file_contents();
        if !errors.print(files) {
            // There were errors!
            return;
        }

        let entry_point = match program.get_entry_point() {
            Some(value) => value,
            None => {
                println!("Expected '#entry' to denote an entry point, and for that entry point to be of type 'fn()'");
                return;
            }
        };

        let backends = std::mem::take(&mut program.backends);
        backends.emit(&program, backend_emitters);

        let elapsed = time.elapsed();
        println!("Finished in {:.4} seconds", elapsed.as_secs_f32());

        if options.run {
            let routine = program.get_routine(entry_point).unwrap();
            if let ir::Routine::UserDefined(routine) = &*routine {
                let mut stack = interp::Stack::new(1 << 16);

                // @Improvement: We want to put the entry point in here.
                match interp::interp(&program, &mut stack, routine, &mut vec![]) {
                    Ok(_) => {}
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
    }

    profile::finish("target\\profile_output.json");
}
