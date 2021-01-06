use crate::dependencies::DependencyList;
use crate::errors::ErrorCtx;
use crate::location::Location;
use crate::program::{MemberMetaData, Program, ScopeId, Task};
use bumpalo::Bump;
use crossbeam::queue::SegQueue;
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
pub fn run(program: &mut Program, num_threads: usize) -> (String, ErrorCtx) {
    let mut allocators: Vec<_> = std::iter::repeat_with(Bump::new)
        .take(num_threads)
        .collect();
    let mut allocators = allocators.iter_mut();

    let borrow_program = &*program;
    let mut threads = Vec::new();
    for (_, allocator) in (1..num_threads).zip(&mut allocators) {
        let allocator_static = unsafe { std::mem::transmute::<_, &'static mut Bump>(allocator) };
        let program_static = unsafe { std::mem::transmute::<_, &'static Program>(borrow_program) };
        threads.push(std::thread::spawn(move || {
            let allocator = unsafe { std::mem::transmute::<_, &mut Bump>(allocator_static) };
            let program_static = unsafe { std::mem::transmute::<_, &Program>(program_static) };
            worker(allocator, program_static)
        }));
    }

    let (thread_context, mut errors) = worker(allocators.next().unwrap(), borrow_program);

    let mut c_headers = String::new();
    c_headers.push_str("#include <stdint.h>\n");
    c_headers.push_str("#include <stdio.h>\n");
    c_headers.push_str("#include <string.h>\n");
    c_headers.push_str("#include <stdlib.h>\n");
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

fn worker<'a>(alloc: &'a mut Bump, program: &'a Program) -> (ThreadContext<'a>, ErrorCtx) {
    let mut errors = ErrorCtx::new();
    let work = program.work();

    let mut thread_context = ThreadContext {
        alloc,
        c_headers: String::new(),
        c_declarations: String::new(),
    };

    loop {
        if let Some(task) = work.queue.pop() {
            match task {
                Task::Parse(meta_data, file) => parse_file(&mut errors, program, &file, meta_data),
                Task::TypeMember(member_id, locals, ast) => {
                    use crate::typer::ast::NodeKind;

                    match crate::typer::process_ast(
                        &mut errors,
                        &mut thread_context,
                        program,
                        locals,
                        &ast,
                        None,
                    ) {
                        Ok((dependencies, locals, ast)) => {
                            let meta_data = match ast.kind() {
                                NodeKind::Global(_, meta_data) => (&**meta_data).clone(),
                                _ => MemberMetaData::None,
                            };
                            let type_ = ast.type_();

                            if type_.can_be_stored_in_constant() {
                                program.logger.log(format_args!(
                                    "type '{}' {:?}",
                                    program.member_name(member_id),
                                    ast.type_(),
                                ));

                                program.set_type_of_member(member_id, type_, meta_data);
                                program.queue_task(
                                    dependencies,
                                    program.member_name(member_id),
                                    Task::EmitMember(member_id, locals, ast),
                                );
                            } else {
                                errors.error(ast.loc, format!("'{}' cannot be stored in a constant, because it contains types that the compiler cannot reason about properly, such as '&any', '[] any', or similar", type_));
                            }
                        }
                        Err(()) => {
                            // TODO: Here we want to poison the Value parameter of the thing this
                            // Task is associated with.
                        }
                    }
                }
                Task::EmitMember(member_id, locals, ast) => {
                    use crate::typer::NodeKind;

                    program.logger.log(format_args!(
                        "emitting member '{}' {:?}",
                        program.member_name(member_id),
                        ast.type_(),
                    ));

                    match ast.kind() {
                        NodeKind::Constant(result) => {
                            program.logger.log(format_args!(
                                "value(at emitting step, through shortcut) '{}'",
                                program.member_name(member_id),
                            ));

                            program.set_value_of_member(member_id, result.as_ptr());
                        }
                        NodeKind::Global(aliasing, _) => {
                            program.logger.log(format_args!(
                                "value(at emitting step, through shortcut) '{}'",
                                program.member_name(member_id),
                            ));

                            let result = program.get_value_of_member(*aliasing);
                            program.set_value_of_member(member_id, result.as_ptr());
                        }
                        _ => {
                            let (calling, routine) =
                                crate::emit::emit(&mut thread_context, program, locals, &ast);

                            let mut dependencies = DependencyList::new();
                            dependencies.calling = calling;
                            program.queue_task(
                                dependencies,
                                program.member_name(member_id),
                                Task::EvaluateMember(member_id, routine),
                            );
                        }
                    }
                }
                Task::EvaluateMember(member_id, routine) => {
                    let mut stack = crate::interp::Stack::new(2048);

                    let result = crate::interp::interp(program, &mut stack, &routine);

                    program
                        .logger
                        .log(format_args!("value '{}'", program.member_name(member_id),));

                    program.set_value_of_member(member_id, result.as_ptr());
                }
                Task::TypeFunction(function_id, locals, ast, return_type, type_) => {
                    use crate::typer::ast::NodeKind;

                    program
                        .logger
                        .log(format_args!("typing function '{:?}'", function_id));

                    match crate::typer::process_ast(
                        &mut errors,
                        &mut thread_context,
                        program,
                        locals,
                        &ast,
                        Some(return_type),
                    ) {
                        Ok((dependencies, locals, ast)) => {
                            program.queue_task(
                                dependencies,
                                "Hello function!".into(),
                                Task::EmitFunction(function_id, locals, ast, type_),
                            );
                        }
                        Err(()) => {
                            // TODO: Here we want to poison the Value parameter of the thing this
                            // Task is associated with.
                        }
                    }
                }
                Task::EmitFunction(function_id, locals, ast, type_) => {
                    use crate::typer::ast::NodeKind;

                    program
                        .logger
                        .log(format_args!("emitting function '{:?}'", function_id));

                    crate::emit::emit_function_declaration(
                        &mut thread_context,
                        program,
                        locals,
                        &ast,
                        type_,
                        function_id,
                    );
                }
            }

            work.tasks_left.fetch_sub(1, Ordering::SeqCst);
        } else if work.tasks_left.load(Ordering::SeqCst) == 0 {
            break;
        }
    }

    (thread_context, errors)
}

fn parse_file(
    errors: &mut ErrorCtx,
    program: &Program,
    file: &Path,
    meta_data: Option<(Location, ScopeId)>,
) {
    let file_name_str = file.to_str().expect("File path is not a valid string, this should not happen since all paths are constructed from strings originally").into();

    // If the file has already been parsed, do not parse it again!
    let mut loaded_files = program.loaded_files.lock();
    if let Some(&scope) = loaded_files.get(&file_name_str) {
        drop(loaded_files);

        program.logger.log(format_args!(
            "File {} was already loaded, so didn't parse it again",
            file_name_str
        ));

        if let Some((loc, imported_from)) = meta_data {
            let _ = program.insert_wildcard_export(errors, loc, scope, imported_from);
        }
    } else {
        match std::fs::read_to_string(&file) {
            Ok(string) => {
                let scope = program.create_scope();

                loaded_files.insert(file_name_str, scope);
                drop(loaded_files);

                let _ =
                    crate::parser::process_string(errors, program, file_name_str, &string, scope);

                program.insert_file_contents(file_name_str, string);

                if let Some((loc, imported_from)) = meta_data {
                    let _ = program.insert_wildcard_export(errors, loc, scope, imported_from);
                }
            }
            Err(_) => {
                if let Some((loc, _)) = meta_data {
                    errors.error(loc, format!("File {:?} cannot be loaded", file));
                } else {
                    errors.global_error(format!("File {:?} cannot be loaded", file));
                }
            }
        }
    }
}
