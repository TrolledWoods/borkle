use crate::errors::ErrorCtx;
use crate::program::{MemberMetaData, Program, Task};
use bumpalo::Bump;
use parking_lot::Mutex;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread::spawn;

pub struct WorkPile {
    pub queue: Mutex<VecDeque<Task>>,
    num_currently_working: AtomicU32,
}

impl WorkPile {
    pub fn new() -> Self {
        Self {
            queue: Mutex::new(VecDeque::new()),
            num_currently_working: AtomicU32::new(0),
        }
    }
}

/// Tries to run everything in the program
pub fn run(program: &Program, num_threads: usize) -> (String, ErrorCtx) {
    let mut allocators: Vec<_> = std::iter::repeat_with(Bump::new)
        .take(num_threads)
        .collect();
    let mut allocators = allocators.iter_mut();

    let mut threads = Vec::new();
    for (_, allocator) in (1..num_threads).zip(&mut allocators) {
        let work = unsafe { &*(&program.work as *const _) };
        let program = unsafe { &*(program as *const _) };
        let allocator = unsafe { &mut *(allocator as *mut _) };
        threads.push(spawn(move || worker(allocator, program, work)));
    }

    let (thread_context, mut errors) = worker(allocators.next().unwrap(), program, &program.work);

    let mut c_headers = String::new();
    c_headers.push_str("#include <stdint.h>\n");
    c_headers.push_str("#include <stdio.h>\n");
    c_headers.push('\n');

    if program.arguments.release {
        crate::c_backend::append_c_type_headers(&mut c_headers);
    }
    c_headers.push_str(&thread_context.c_headers);

    let ThreadContext {
        mut c_declarations, ..
    } = thread_context;

    if program.arguments.release {
        for thread in threads {
            let (ctx, other_errors) = thread.join().unwrap();
            c_headers.push_str(&ctx.c_headers);
            c_declarations.push_str(&ctx.c_declarations);
            errors.join(other_errors);
        }

        crate::c_backend::declare_constants(&mut c_headers, program);
        crate::c_backend::instantiate_constants(&mut c_headers, program);
        c_headers.push_str(&c_declarations);
    } else {
        for thread in threads {
            let (_, other_errors) = thread.join().unwrap();
            errors.join(other_errors);
        }
    }

    program.check_for_completion(&mut errors);

    (c_headers, errors)
}

/// Data that is local to each thread. This is useful to have because
/// it lets us reduce the amount of syncronisation necessary, and instead just
/// combine all the collective thread data at the end of the compilation.
pub struct ThreadContext<'a> {
    pub alloc: &'a mut Bump,
    pub c_headers: String,
    pub c_declarations: String,
}

fn worker<'a>(
    alloc: &'a mut Bump,
    program: &'a Program,
    work: &WorkPile,
) -> (ThreadContext<'a>, ErrorCtx) {
    let mut errors = ErrorCtx::new();

    let mut thread_context = ThreadContext {
        alloc,
        c_headers: String::new(),
        c_declarations: String::new(),
    };

    loop {
        // We explicitly take the lock here so that we make sure to increase
        // the number of currently working threads BEFORE dropping the lock.
        // This is vital as otherwise threads might think that there is no work
        // left to do even though there might be some.
        let mut queue_lock = work.queue.lock();
        if let Some(task) = queue_lock.pop_back() {
            // We have to increase the number of currently working threads before
            // releasing the lock
            let currently_working_counter = Count::new(&work.num_currently_working);

            drop(queue_lock);

            match task {
                Task::Parse(file) => match std::fs::read_to_string(&file) {
                    Ok(string) => {
                        let file_name_str = file.to_str().expect("File path is not a valid string, this should not happen since all paths are constructed from strings originally").into();

                        // If the file has already been parsed, do not parse it again!
                        if !program.loaded_files.lock().insert(file_name_str) {
                            program.logger.log(format_args!(
                                "File {} was already loaded, so didn't parse it again",
                                file_name_str
                            ));
                        } else {
                            let _ = crate::parser::process_string(
                                &mut errors,
                                program,
                                file_name_str,
                                &string,
                            );
                        }
                    }
                    Err(_) => {
                        errors.global_error(format!("File {:?} cannot be loaded", file));
                    }
                },
                Task::Type(member_id, locals, ast) => {
                    use crate::typer::ast::NodeKind;

                    match crate::typer::process_ast(
                        &mut errors,
                        &mut thread_context,
                        program,
                        locals,
                        &ast,
                    ) {
                        Ok((dependencies, locals, ast)) => {
                            let meta_data = match ast.kind() {
                                NodeKind::FunctionDeclaration {
                                    locals: _,
                                    body: _,
                                    arg_names,
                                    default_values,
                                } => MemberMetaData::Function {
                                    arg_names: arg_names.clone(),
                                    default_values: default_values.clone(),
                                },
                                _ => MemberMetaData::None,
                            };
                            let type_ = ast.type_();

                            program.logger.log(format_args!(
                                "type '{}' {:?}",
                                program.member_name(member_id),
                                ast.type_(),
                            ));

                            program.set_type_of_member(member_id, type_, meta_data);
                            program.queue_task(
                                member_id,
                                dependencies,
                                Task::Value(member_id, locals, ast),
                            );
                        }
                        Err(()) => {
                            // TODO: Here we want to poison the Value parameter of the thing this
                            // Task is associated with.
                        }
                    }
                }
                Task::Value(member_id, locals, ast) => {
                    use crate::typer::NodeKind;

                    match ast.kind() {
                        NodeKind::Constant(constant) => {
                            program.set_value_of_member(member_id, constant.as_ptr());
                        }
                        _ => {
                            let routine =
                                crate::ir::emit::emit(&mut thread_context, program, locals, &ast);
                            let mut stack = crate::interp::Stack::new(2048);

                            let result = crate::interp::interp(program, &mut stack, &routine);

                            program.logger.log(format_args!(
                                "value '{}' {}",
                                program.member_name(member_id),
                                unsafe { *(result as *const u64) }
                            ));

                            program.set_value_of_member(member_id, result);
                        }
                    }
                }
            }

            // We have to decrease the number of currently working threads after
            // the work is done, otherwise we may be pushing more work after
            // saying nobody is working, which could cause incorrect thread stopping.
            drop(currently_working_counter);
        } else {
            // This has to happen before the drop, because otherwise another thread
            // might push another piece of work and decrement the currently working counter,
            // and that would cause this thread to incorrectly stop working.
            let currently_working = work.num_currently_working.load(Ordering::SeqCst);
            drop(queue_lock);

            if currently_working == 0 {
                break;
            }
        }
    }

    (thread_context, errors)
}

struct Count<'a>(&'a AtomicU32);

impl<'a> Count<'a> {
    fn new(atomic: &'a AtomicU32) -> Self {
        atomic.fetch_add(1, Ordering::SeqCst);
        Self(atomic)
    }
}

impl Drop for Count<'_> {
    fn drop(&mut self) {
        self.0.fetch_sub(1, Ordering::SeqCst);
    }
}
