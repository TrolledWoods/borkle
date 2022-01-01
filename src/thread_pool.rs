use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::location::Location;
use crate::type_infer::{AstVariantId, ValueId as TypeId};
use crate::program::{MemberMetaData, Program, ScopeId, Task};
use bumpalo::Bump;
// use crossbeam::queue::SegQueue;
use parking_lot::Mutex;
use std::path::Path;
use std::sync::atomic::{AtomicU32, Ordering};

pub struct WorkPile {
    queue: Mutex<Vec<Task>>,
    tasks_left: AtomicU32,
}

impl WorkPile {
    pub fn new() -> Self {
        Self {
            queue: Mutex::new(Vec::new()),
            tasks_left: AtomicU32::new(0),
        }
    }

    pub fn enqueue(&self, task: Task) {
        self.tasks_left.fetch_add(1, Ordering::SeqCst);
        self.queue.lock().insert(0, task);
    }

    pub fn dequeue(&self) -> Option<Task> {
        let mut queue = self.queue.lock();
        queue.pop()
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
    if program.arguments.release {
        c_headers.push_str(crate::c_backend::BOILER_PLATE);
        crate::c_backend::declare_types(&mut c_headers);
        c_headers.push_str(&thread_context.c_headers);
    }

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
                Task::FlagPolyMember(_, MemberDep::Type, _) => {
                    unreachable!("Can't flag poly member as type, should use Task::TypePolyMember instead");
                    profile::profile!("Task::FlagPolyMember Type");

                }
                Task::FlagPolyMember(_, MemberDep::Value, _) => {
                    unreachable!("Flag poly member with just a value should never happen");
                }
                Task::FlagPolyMember(poly_member, MemberDep::ValueAndCallableIfFunction, _) => {
                    profile::profile!("Task::FlagPolyMember Value");
                    program.logger.log(format_args!(
                        "flagged poly member is value and callable '{}'",
                        program.poly_member_name(poly_member),
                    ));
                    program.flag_poly_member_value(poly_member);
                    program.flag_poly_member_value_and_callable_if_function(poly_member);
                }

                Task::Parse(meta_data, file) => {
                    profile::profile!("Parse");
                    parse_file(&mut errors, program, &file, meta_data);
                }
                Task::TypePolyMember { member_id, ast, locals, mut dependencies, poly_args } => {
                    profile::profile!("Task::TypePolyMember");

                    let mut yield_data = crate::typer::begin(&mut errors, &mut thread_context, program, locals, ast, poly_args);
                    crate::typer::solve(&mut errors, &mut thread_context, program, &mut yield_data);

                    program.set_yield_data_of_poly_member(member_id, yield_data);

                    program.logger.log(format_args!(
                        "typed poly member {}",
                        program.poly_member_name(member_id),
                    ));
                    program.flag_poly_member_type(member_id);

                    // TODO: We should read the deps from the typer instead, it should know what the deps are after `begin`.
                    dependencies.set_minimum_member_dep(MemberDep::ValueAndCallableIfFunction);
                    program.queue_task(
                        dependencies,
                        Task::FlagPolyMember(
                            member_id,
                            MemberDep::ValueAndCallableIfFunction,
                            DependencyList::new(), // Since the next thing ignores its dependencies anyway, we don't care to pass it. This might change later though
                        ),
                    );
                }
                Task::TypeMember { member_id, ast, locals } => {
                    // If it's a polymorphic thing this task could have been scheduled twice, so we have to do this check.
                    if !program.member_is_typed(member_id) {
                        profile::profile!("Task::TypeMember");
                        use crate::parser::NodeKind;

                        match crate::typer::process_ast(
                            &mut errors,
                            &mut thread_context,
                            program,
                            locals,
                            ast,
                        ) {
                            Ok(Ok((dependencies, locals, types, ast, additional_info))) => {
                                let meta_data = match &ast.root().kind {
                                    NodeKind::Constant(_, Some(meta_data)) => {
                                        (&**meta_data).clone()
                                    }
                                    NodeKind::ResolvedGlobal(_, meta_data) => {
                                        (&**meta_data).clone()
                                    }
                                    _ => MemberMetaData::None,
                                };

                                let type_ = types.value_to_compiler_type(TypeId::Node(AstVariantId::root(), ast.root().id));

                                if type_.can_be_stored_in_constant() {
                                    program.logger.log(format_args!(
                                        "type '{}' {:?}",
                                        program.member_name(member_id),
                                        type_,
                                    ));

                                    program.set_type_of_member(member_id, type_, meta_data);
                                    program.queue_task(
                                        dependencies,
                                        Task::EmitMember(member_id, locals, types, additional_info, ast),
                                    );
                                } else {
                                    errors.error(ast.root().loc, format!("'{}' cannot be stored in a constant, because it contains types that the compiler cannot reason about properly, such as '&any', '[] any', or similar", type_));
                                }
                            }
                            Ok(Err(_)) => {
                                todo!("Continue typing member");
                                /*program.queue_task(
                                    dependencies,
                                    Task::ContinueTypingMember { member_id, yield_info },
                                );*/
                            }
                            Err(()) => {
                                // TODO: Here we want to poison the Value parameter of the thing this
                                // Task is associated with.
                            }
                        }
                    }
                }
                Task::EmitMember(member_id, mut locals, mut types, additional_info, ast) => {
                    if !program.member_is_evaluated(member_id) {
                        profile::profile!("Task::EmitMember");
                        use crate::typer::NodeKind;

                        let type_ = types.value_to_compiler_type(TypeId::Node(AstVariantId::root(), ast.root_id()));
                        program.logger.log(format_args!(
                            "emitting member '{}' {:?}",
                            program.member_name(member_id),
                            type_,
                        ));

                        let (calling, routine) = crate::emit::emit(
                            &mut thread_context,
                            program,
                            &mut locals,
                            &mut types,
                            &ast,
                            &additional_info,
                            ast.root_id(),
                            AstVariantId::root(),
                        );

                        let mut dependencies = DependencyList::new();
                        for call in calling {
                            // FIXME: This should include the location of the call
                            dependencies
                                .add(ast.root().loc, DepKind::Callable(call));
                        }
                        program.queue_task(
                            dependencies,
                            Task::EvaluateMember(member_id, routine),
                        );
                    }
                }
                Task::EvaluateMember(member_id, routine) => {
                    if !program.member_is_evaluated(member_id) {
                        let mut stack = crate::interp::Stack::new(2048);

                        match crate::interp::interp(program, &mut stack, &routine, &mut vec![]) {
                            Ok(result) => {
                                let type_ = program.get_member_type(member_id);

                                let value = program.insert_buffer(type_, result.as_ptr());

                                program
                                    .logger
                                    .log(format_args!("value '{}': {}", program.member_name(member_id), crate::program::constant_to_str(type_, value, 0)));

                                program.set_value_of_member(member_id, value);
                                program.flag_member_callable(member_id);

                                for function_id in unsafe { type_.get_function_ids(value.as_ptr()) } {
                                    program.flag_function_callable(function_id);
                                }
                            }
                            Err(call_stack) => {
                                for &caller in call_stack.iter().rev().skip(1) {
                                    errors.info(caller, "".to_string());
                                }

                                errors.error(*call_stack.last().unwrap(), "Assert failed!".to_string());
                            }
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
                Task::EmitFunction(mut locals, mut types, additional_info, ast, node_id, type_, function_id, ast_variant_id) => {
                    program
                        .logger
                        .log(format_args!("emitting function '{:?}'", function_id));

                    let loc = program.get_function_loc(function_id);

                    crate::emit::emit_function_declaration(
                        &mut thread_context,
                        program,
                        &mut locals,
                        &mut types,
                        &ast,
                        &additional_info,
                        node_id,
                        ast_variant_id,
                        type_,
                        loc,
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
