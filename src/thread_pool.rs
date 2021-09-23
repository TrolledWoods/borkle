use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::location::Location;
use crate::program::{MemberMetaData, Program, ScopeId, Task};
use bumpalo::Bump;
// use crossbeam::queue::SegQueue;
use parking_lot::Mutex;
use std::path::Path;
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::Instant;

pub struct WorkPile {
    queue: Mutex<Vec<Task>>,
    start: Instant,
    tasks_left: AtomicU32,
}

impl WorkPile {
    pub fn new() -> Self {
        Self {
            queue: Mutex::new(Vec::new()),
            start: Instant::now(),
            tasks_left: AtomicU32::new(0),
        }
    }

    pub fn enqueue(&self, task: Task) {
        self.tasks_left.fetch_add(1, Ordering::SeqCst);
        self.queue.lock().insert(0, task);
    }

    pub fn dequeue(&self) -> Option<Task> {
        // FIXME: This is only for finding bugs early purposes; it's not for actualy real use, in
        // the future we want to make a proper scheduler that picks tasks appropriately depending
        // on the circumstances.
        let mut queue = self.queue.lock();
        if queue.len() > 0 {
            let seed = self.start.elapsed().as_nanos() as usize;
            let i = seed % queue.len();
            Some(queue.remove(i))
        } else {
            None
        }
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
    profile::profile!("Worker thread loop");

    let mut errors = ErrorCtx::new();
    let work = program.work();

    let mut thread_context = ThreadContext {
        alloc,
        c_headers: String::new(),
        c_declarations: String::new(),
    };

    loop {
        if let Some(task) = work.dequeue() {
            match task {
                Task::FlagPolyMember(poly_member, MemberDep::Type, mut deps) => {
                    profile::profile!("Task::FlagPolyMember Type");

                    program.logger.log(format_args!(
                        "flagged poly member is typeable '{:?}'",
                        poly_member
                    ));
                    program.flag_poly_member(poly_member, MemberDep::Type);

                    deps.set_minimum_member_dep(MemberDep::ValueAndCallableIfFunction);
                    program.queue_task(
                        deps,
                        Task::FlagPolyMember(
                            poly_member,
                            MemberDep::Value,
                            DependencyList::new(), // Since the next thing ignores its dependencies anyway, we don't care to pass it. This might change later though
                        ),
                    );
                }
                Task::FlagPolyMember(poly_member, MemberDep::Value, _) => {
                    profile::profile!("Task::FlagPolyMember Value");
                    program.logger.log(format_args!(
                        "flagged poly member is value and callable '{:?}'",
                        poly_member
                    ));
                    program.flag_poly_member(poly_member, MemberDep::Value);
                    program.flag_poly_member(poly_member, MemberDep::ValueAndCallableIfFunction);
                }
                // FIXME: Think about if we can be less conservative and use this anyway.
                Task::FlagPolyMember(_, MemberDep::ValueAndCallableIfFunction, _) => {}

                Task::Parse(meta_data, file) => {
                    profile::profile!("Parse");
                    parse_file(&mut errors, program, &file, meta_data);
                },
                Task::TypeMember(member_id, locals, ast) => {
                    // If it's a polymorphic thing anything could have happened, honestly
                    if !program.member_is_typed(member_id) {
                        profile::profile!("Task::TypeMember");
                        use crate::parser::ast::NodeKind;

                        match crate::typer::process_ast(
                            &mut errors,
                            &mut thread_context,
                            program,
                            locals,
                            ast,
                            None,
                            &[],
                        ) {
                            Ok((dependencies, locals, ast)) => {
                                let meta_data = match &ast.get(ast.root).kind {
                                    NodeKind::Constant(_, Some(meta_data)) => {
                                        (&**meta_data).clone()
                                    }
                                    NodeKind::ResolvedGlobal(_, meta_data) => (&**meta_data).clone(),
                                    _ => MemberMetaData::None,
                                };
                                let type_ = ast.get(ast.root).type_();

                                if type_.can_be_stored_in_constant() {
                                    program.logger.log(format_args!(
                                        "type '{}' {:?}",
                                        program.member_name(member_id),
                                        ast.get(ast.root).type_(),
                                    ));

                                    program.set_type_of_member(member_id, type_, meta_data);
                                    program.queue_task(
                                        dependencies,
                                        Task::EmitMember(member_id, locals, ast),
                                    );
                                } else {
                                    errors.error(ast.get(ast.root).loc, format!("'{}' cannot be stored in a constant, because it contains types that the compiler cannot reason about properly, such as '&any', '[] any', or similar", type_));
                                }
                            }
                            Err(()) => {
                                // TODO: Here we want to poison the Value parameter of the thing this
                                // Task is associated with.
                            }
                        }
                    }
                }
                Task::EmitMember(member_id, locals, ast) => {
                    if !program.member_is_evaluated(member_id) {
                        profile::profile!("Task::EmitMember");
                        use crate::typer::NodeKind;

                        program.logger.log(format_args!(
                            "emitting member '{}' {:?}",
                            program.member_name(member_id),
                            ast.get(ast.root).type_(),
                        ));

                        match &ast.get(ast.root).kind {
                            NodeKind::Constant(result, _) => {
                                program.logger.log(format_args!(
                                    "value(at emitting step, through shortcut) '{}'",
                                    program.member_name(member_id),
                                ));

                                program.set_value_of_member(member_id, *result);

                                // Flag the member as callable once all the function pointers inside
                                // the type are also callable. FIXME: This doesn't work for function
                                // pointers behind other pointers yet!
                                let mut dependencies = DependencyList::new();
                                for function_id in
                                    unsafe { ast.get(ast.root).type_().get_function_ids(result.as_ptr()) }
                                {
                                    dependencies.add(ast.get(ast.root).loc, DepKind::Callable(function_id));
                                }

                                program
                                    .queue_task(dependencies, Task::FlagMemberCallable(member_id));
                            }
                            NodeKind::ResolvedGlobal(aliasing, _) => {
                                program.logger.log(format_args!(
                                    "value(at emitting step, through shortcut) '{}'",
                                    program.member_name(member_id),
                                ));

                                let result = program.get_value_of_member(*aliasing);
                                program.set_value_of_member(member_id, result);

                                // Flag the member as callable once all the function pointers inside
                                // the type are also callable. FIXME: This doesn't work for function
                                // pointers behind other pointers yet!
                                let mut dependencies = DependencyList::new();
                                for function_id in
                                    unsafe { ast.get(ast.root).type_().get_function_ids(result.as_ptr()) }
                                {
                                    dependencies.add(ast.get(ast.root).loc, DepKind::Callable(function_id));
                                }

                                program
                                    .queue_task(dependencies, Task::FlagMemberCallable(member_id));
                            }
                            _ => {
                                let (calling, routine) =
                                    crate::emit::emit(&mut thread_context, program, locals, &ast, ast.root);

                                let mut dependencies = DependencyList::new();
                                for call in calling {
                                    // FIXME: This should include the location of the call
                                    dependencies.add(ast.get(ast.root).loc, DepKind::Callable(call));
                                }
                                program.queue_task(
                                    dependencies,
                                    Task::EvaluateMember(member_id, routine),
                                );
                            }
                        }
                    }
                }
                Task::EvaluateMember(member_id, routine) => {
                    if !program.member_is_evaluated(member_id) {
                        let mut stack = crate::interp::Stack::new(2048);

                        let result = crate::interp::interp(program, &mut stack, &routine);

                        program
                            .logger
                            .log(format_args!("value '{}'", program.member_name(member_id),));

                        let type_ = program.get_member_type(member_id);
                        let value = program.insert_buffer(type_, result.as_ptr());

                        program.set_value_of_member(member_id, value);
                        program.flag_member_callable(member_id);

                        for function_id in unsafe { type_.get_function_ids(value.as_ptr()) } {
                            program.flag_function_callable(function_id);
                        }
                    }
                }
                Task::FlagMemberCallable(member_id) => {
                    if !program.member_is_callable(member_id) {
                        program.flag_member_callable(member_id);

                        let (value, type_) = program.get_member_value(member_id);

                        for function_id in unsafe { type_.get_function_ids(value.as_ptr()) } {
                            program.flag_function_callable(function_id);
                        }
                    }
                }
                Task::TypeFunction(function_id, locals, ast, return_type, type_, poly_args) => {
                    program
                        .logger
                        .log(format_args!("typing function '{:?}'", function_id));

                    match crate::typer::process_ast(
                        &mut errors,
                        &mut thread_context,
                        program,
                        locals,
                        ast,
                        Some(return_type),
                        &poly_args,
                    ) {
                        Ok((dependencies, locals, ast)) => {
                            program.queue_task(
                                dependencies,
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
