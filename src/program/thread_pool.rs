use crate::errors::ErrorCtx;
use crate::program::{MemberMetaData, Program, Task};
use bumpalo::Bump;
use crossbeam::queue::SegQueue;
use crossbeam::scope;
use std::path::Path;
use std::sync::atomic::{AtomicU32, Ordering};

pub struct WorkPile {
    queue: SegQueue<Task>,
    tasks_left: AtomicU32,
}

impl WorkPile {
    pub fn new() -> Self {
        Self {
            queue: SegQueue::new(),
            tasks_left: AtomicU32::new(0),
        }
    }

    pub fn enqueue(&self, task: Task) {
        self.tasks_left.fetch_add(1, Ordering::SeqCst);
        self.queue.push(task);
    }
}

/// Tries to evaluate everything in the program
pub fn run(program: &Program, num_threads: usize) -> (String, ErrorCtx) {
    let mut allocators: Vec<_> = std::iter::repeat_with(Bump::new)
        .take(num_threads)
        .collect();
    let mut allocators = allocators.iter_mut();

    scope(|s| {
        let mut threads = Vec::new();
        for (_, allocator) in (1..num_threads).zip(&mut allocators) {
            threads.push(s.spawn(move |_| worker(allocator, program)));
        }

        let (thread_context, mut errors) = worker(allocators.next().unwrap(), program);

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
    })
    .unwrap()
}

/// Data that is local to each thread. This is useful to have because
/// it lets us reduce the amount of syncronisation necessary, and instead just
/// combine all the collective thread data at the end of the compilation.
pub struct ThreadContext<'a> {
    pub alloc: &'a mut Bump,
    pub c_headers: String,
    pub c_declarations: String,
}

fn worker<'a>(alloc: &'a mut Bump, program: &'a Program) -> (ThreadContext<'a>, ErrorCtx) {
    let mut errors = ErrorCtx::new();
    let work = &program.work;

    let mut thread_context = ThreadContext {
        alloc,
        c_headers: String::new(),
        c_declarations: String::new(),
    };

    loop {
        if let Some(task) = work.queue.pop() {
            match task {
                Task::Parse(file) => parse_file(&mut errors, program, &file),
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
                                NodeKind::Global(_, meta_data) => (&**meta_data).clone(),
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
                                crate::emit::emit(&mut thread_context, program, locals, &ast);
                            let mut stack = crate::interp::Stack::new(2048);

                            let result = crate::interp::interp(program, &mut stack, &routine);

                            program
                                .logger
                                .log(format_args!("value '{}'", program.member_name(member_id),));

                            program.set_value_of_member(member_id, result.as_ptr());
                        }
                    }
                }
            }

            work.tasks_left.fetch_sub(1, Ordering::SeqCst);
        } else if work.tasks_left.load(Ordering::SeqCst) == 0 {
            break;
        }
    }

    (thread_context, errors)
}

fn parse_file(errors: &mut ErrorCtx, program: &Program, file: &Path) {
    match std::fs::read_to_string(&file) {
        Ok(string) => {
            let file_name_str = file.to_str().expect("File path is not a valid string, this should not happen since all paths are constructed from strings originally").into();

            // If the file has already been parsed, do not parse it again!
            if !program.loaded_files.lock().insert(file_name_str) {
                program.logger.log(format_args!(
                    "File {} was already loaded, so didn't parse it again",
                    file_name_str
                ));
            } else {
                let _ = crate::parser::process_string(errors, program, file_name_str, &string);
            }
        }
        Err(_) => {
            errors.global_error(format!("File {:?} cannot be loaded", file));
        }
    }
}
