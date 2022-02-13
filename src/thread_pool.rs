use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::location::Location;
use crate::type_infer::{AstVariantId, ValueId as TypeId};
use crate::program::{Program, ScopeId, Task, MemberKind};
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
pub fn run(program: &mut Program, num_threads: usize) -> ErrorCtx {
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

    let (_thread_context, mut errors) = worker(allocators.next().unwrap(), borrow_program);

    for thread in threads {
        let (_ctx, other_errors) = thread.join().unwrap();
        errors.join(other_errors);
    }

    program.check_for_completion(&mut errors);

    errors
}

/// Data that is local to each thread. This is useful to have because
/// it lets us reduce the amount of syncronisation necessary, and instead just
/// combine all the collective thread data at the end of the compilation.
pub struct ThreadContext<'a> {
    pub alloc: &'a mut Bump,
}

fn worker<'a>(alloc: &'a mut Bump, program: &'a Program) -> (ThreadContext<'a>, ErrorCtx) {
    profile::profile!("Worker thread loop");

    let mut errors = ErrorCtx::new();
    let work = program.work();

    let mut thread_context = ThreadContext {
        alloc,
    };

    loop {
        if let Some(task) = work.dequeue() {
            match task {
                Task::FlagPolyMember(_, MemberDep::Type, _) => {
                    unreachable!("Can't flag poly member as type, should use Task::TypePolyMember instead");
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

                Task::Parse { imported_at, path, is_library } => {
                    profile::profile!("Parse");
                    parse_file(&mut errors, program, &path, imported_at, is_library);
                }
                Task::TypePolyMember { member_id, ast, member_kind, locals, mut dependencies, poly_args } => {
                    profile::profile!("Task::TypePolyMember");

                    let (mut yield_data, meta_data) = crate::typer::begin(&mut errors, &mut thread_context, program, locals, ast, poly_args, member_kind);
                    crate::typer::solve(&mut errors, &mut thread_context, program, &mut yield_data);

                    program.set_yield_data_of_poly_member(member_id, yield_data);

                    program.logger.log(format_args!(
                        "typed poly member {} {:?}",
                        program.poly_member_name(member_id),
                        meta_data,
                    ));
                    program.flag_poly_member_type(member_id, meta_data);

                    if member_kind == MemberKind::Const {
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
                    } else {
                        // OMEGA HACK!!!! To work with type expressions
                        program.flag_poly_member_value(member_id);
                        program.flag_poly_member_value_and_callable_if_function(member_id);
                    }
                }
                Task::TypeMember { member_id, member_kind, ast, locals } => {
                    // If it's a polymorphic thing this task could have been scheduled twice, so we have to do this check.
                    if !program.member_is_typed(member_id) {
                        profile::profile!("Task::TypeMember");

                        match crate::typer::process_ast(
                            &mut errors,
                            &mut thread_context,
                            program,
                            locals,
                            ast,
                            member_kind,
                        ) {
                            Ok((Ok((dependencies, locals, types, ast, root_type_id, additional_info)), meta_data)) => {
                                let type_ = types.value_to_compiler_type(root_type_id);

                                program.logger.log(format_args!(
                                    "type '{}' {:?} {:?}",
                                    program.member_name(member_id),
                                    type_,
                                    meta_data,
                                ));

                                program.set_type_of_member(member_id, type_, meta_data);

                                if member_kind == MemberKind::Const {
                                    program.queue_task(
                                        dependencies,
                                        Task::EmitMember(member_id, locals, types, additional_info, ast),
                                    );
                                } else {
                                    // OMEGA HACK!!!! To work with type expressions
                                    program.set_value_of_member(member_id, crate::program::constant::ConstantRef::dangling());
                                    program.flag_member_callable(member_id);
                                }
                            }
                            Ok((Err(_), _)) => {
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
                            false,
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
                        let mut stack = crate::interp::Stack::new(crate::interp::DEFAULT_STACK_SIZE);

                        match crate::interp::interp(program, &mut stack, &routine, &mut vec![]) {
                            Ok(result) => {
                                let type_ = program.get_member_type(member_id);
                                let value = program.insert_buffer(&type_, result.as_ptr());

                                program
                                    .logger
                                    .log(format_args!("value '{}': {}", program.member_name(member_id), crate::program::constant_to_str(&type_, value, 0)));

                                program.set_value_of_member(member_id, value);
                                program.flag_member_callable(member_id);

                                
                                unsafe {
                                    type_.get_function_ids(value.as_ptr(), |function_id| {
                                        program.flag_function_callable(function_id);
                                    });
                                }
                            }
                            Err((message, call_stack)) => {
                                for &caller in call_stack.iter().rev().skip(1) {
                                    errors.info(caller, "".to_string());
                                }

                                errors.error(*call_stack.last().unwrap(), message);
                            }
                        }
                    }
                }
                Task::FlagMemberCallable(member_id) => {
                    if !program.member_is_callable(member_id) {
                        program.flag_member_callable(member_id);

                        let (value, type_) = program.get_member_value(member_id);

                        unsafe {
                            type_.get_function_ids(value.as_ptr(), |function_id| {
                                program.flag_function_callable(function_id);
                            });
                        }
                    }
                }
                Task::EmitFunction(mut locals, mut types, additional_info, ast, node_id, _, function_id, ast_variant_id) => {
                    program
                        .logger
                        .log(format_args!("emitting function '{:?}'", function_id));

                    let loc = program.get_function_loc(function_id);

                    crate::emit::emit_function_declaration(
                        &mut thread_context,
                        program,
                        &mut locals,
                        &mut types,
                        ast.get(node_id),
                        &additional_info,
                        node_id,
                        ast_variant_id,
                        loc,
                        function_id,
                        false,
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
    is_library: bool,
) {
    let file_name_str = format!("{}", file.display()).into();

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

                if let Ok(loc) = crate::parser::process_string(errors, program, file_name_str, &string, scope) {
                    if is_library {
                        program.lib_lines_of_code.fetch_add(loc, Ordering::Relaxed);
                    } else {
                        program.user_lines_of_code.fetch_add(loc, Ordering::Relaxed);
                    }
                }

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
