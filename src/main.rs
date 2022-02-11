#![feature(let_else)]
#![feature(generic_associated_types)]
#![feature(backtrace)]
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

    let _ = enable_ansi_support::enable_ansi_support();

    let time = std::time::Instant::now();
    let logger = logging::Logger::new();

    let args: Vec<_> = std::env::args().skip(1).collect();
    let borrowed_args: Vec<&str> = args.iter().map(|v| &**v).collect();
    if let Some(options) = command_line_arguments::Arguments::from_args(&borrowed_args) {
        if options.num_threads == 0 {
            println!("Has to have at least one thread");
            return;
        }

        let frontend_timer = std::time::Instant::now();

        let mut program = program::Program::new(logger, options.clone());
        program.add_file(&options.file, false);
        
        if !options.no_builtins {
            let mut compiler_path = options.lib_path.clone();
            compiler_path.push("compiler.bo");
            program.add_file(&compiler_path, true);
        }

        let mut errors = thread_pool::run(&mut program, options.num_threads);

        let frontend_time = frontend_timer.elapsed();

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

        let backend_timer = std::time::Instant::now();

        if options.output_ir {
            backend::emit_bir(&program, &options.ir_path);
        }

        if options.output_x64 {
            backend::emit_x64(&program, &options.x64_path);
        }

        let backend_time = backend_timer.elapsed();

        let elapsed = time.elapsed();

        let user_lines = *program.user_lines_of_code.get_mut();
        let lib_lines  = *program.lib_lines_of_code .get_mut();
        println!("Compiled {} lines of code", user_lines + lib_lines);
        println!("      .. {} user code", user_lines);
        println!("      .. {} libraries", lib_lines);

        println!("Finished in {:.6} seconds", elapsed.as_secs_f32());
        println!("         .. {:.6} were frontend", frontend_time.as_secs_f32());
        println!("         .. {:.6} were backend",  backend_time.as_secs_f32());

        if options.run {
            let routine = program.get_routine(entry_point).unwrap();
            if let ir::Routine::UserDefined(routine) = &*routine {
                let mut stack = interp::Stack::new(1 << 16);

                // @Improvement: We want to put the entry point in here.
                match interp::interp(&program, &mut stack, routine, &mut vec![]) {
                    Ok(_) => {}
                    Err((message, call_stack)) => {
                        errors.clear();
                        for &caller in call_stack.iter().rev().skip(1) {
                            errors.info(caller, "".to_string());
                        }

                        errors.error(*call_stack.last().unwrap(), message);
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
