use crate::command_line_arguments::Arguments;
use crate::errors::ErrorCtx;
use crate::logging::Logger;
use crate::program::{Program, Task};
use parking_lot::Mutex;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;
use std::thread::{spawn, JoinHandle};

/// A channel from where you can send work.
///
/// After you `join` the thread pool, adding more work might fail unless that work is 'within'
/// other work; therefore, add all the build files you want, that are not imported through other
/// files, before calling `join`.
#[derive(Clone)]
pub struct WorkSender {
    work: Arc<WorkPile>,
}

impl WorkSender {
    pub fn send(&self, task: Task) {
        self.work.queue.lock().push_front(task);
    }
}

struct WorkPile {
    queue: Mutex<VecDeque<Task>>,
    num_currently_working: AtomicU32,
}

/// This guy is in charge of running all the Tasks that we queue up.
pub struct ThreadPool {
    threads: Vec<JoinHandle<(ThreadContext, ErrorCtx)>>,
    program: Arc<Program>,
    work: Arc<WorkPile>,
}

impl ThreadPool {
    pub fn new(
        options: Box<Arguments>,
        logger: Logger,
        tasks: impl IntoIterator<Item = Task>,
    ) -> Self {
        let work = Arc::new(WorkPile {
            queue: Mutex::new(tasks.into_iter().collect()),
            // Set this to one to begin with so that no thread ever stops working,
            // because before joining the thread pool there may be more work that is
            // pushed onto it.
            num_currently_working: AtomicU32::new(1),
        });
        Self {
            threads: Vec::new(),
            program: Arc::new(Program::new(
                logger,
                WorkSender {
                    work: Arc::clone(&work),
                },
                options,
            )),
            work,
        }
    }

    pub fn spawn_thread(&mut self) {
        let program = Arc::clone(&self.program);
        let work = Arc::clone(&self.work);
        self.threads.push(spawn(move || worker(&program, &work)));
    }

    pub fn program(&self) -> Arc<Program> {
        Arc::clone(&self.program)
    }

    /// Makes the main thread also do work, and finally
    /// joins them all together once the work is done.
    pub fn join(self) -> (String, ErrorCtx) {
        self.work
            .num_currently_working
            .fetch_sub(1, Ordering::SeqCst);
        let (thread_context, mut errors) = worker(&self.program, &self.work);

        let mut c_headers = String::new();
        c_headers.push_str("#include <stdint.h>\n");
        c_headers.push_str("#include <stdio.h>\n");
        c_headers.push('\n');

        if self.program.arguments.release {
            crate::c_backend::append_c_type_headers(&mut c_headers);
        }
        c_headers.push_str(&thread_context.c_headers);

        let ThreadContext {
            c_headers: _,
            mut c_declarations,
        } = thread_context;

        for thread in self.threads {
            let (ctx, other_errors) = thread.join().unwrap();
            c_headers.push_str(&ctx.c_headers);
            c_declarations.push_str(&ctx.c_declarations);
            errors.join(other_errors);
        }

        crate::c_backend::declare_constants(&mut c_headers, &self.program);
        crate::c_backend::instantiate_constants(&mut c_headers, &self.program);
        c_headers.push_str(&c_declarations);

        self.program.check_for_completion(&mut errors);

        (c_headers, errors)
    }
}

/// Data that is local to each thread. This is useful to have because
/// it lets us reduce the amount of syncronisation necessary, and instead just
/// combine all the collective thread data at the end of the compilation.
pub struct ThreadContext {
    pub c_headers: String,
    pub c_declarations: String,
}

fn worker(program: &Arc<Program>, work: &Arc<WorkPile>) -> (ThreadContext, ErrorCtx) {
    let mut errors = ErrorCtx::new();

    let mut thread_context = ThreadContext {
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
                Task::Parse(path) => match std::fs::read_to_string(&path) {
                    Ok(string) => {
                        let _ = crate::parser::process_string(&mut errors, program, path, &string);
                    }
                    Err(_) => {
                        errors.global_error(format!("File {:?} cannot be loaded", path));
                    }
                },
                Task::Type(member_id, locals, ast) => {
                    match crate::typer::process_ast(&mut errors, program, locals, &ast) {
                        Ok((dependencies, locals, ast)) => {
                            let root = ast.root().unwrap();
                            let type_ = root.type_();

                            program.logger.log(format_args!(
                                "type of '{}' = '{:?}'",
                                member_id.to_ustr(),
                                type_
                            ));

                            program.set_type_of_member(member_id.to_ustr(), type_);
                            let _ = program.insert(
                                &mut errors,
                                root.loc,
                                member_id.to_ustr(),
                                dependencies,
                                false,
                                |id| Task::Value(id, locals, ast),
                            );
                        }
                        Err(()) => {
                            // TODO: Here we want to poison the Value parameter of the thing this
                            // Task is associated with.
                        }
                    }
                }
                Task::Value(member_id, locals, ast) => {
                    let routine = crate::ir::emit::emit(&mut thread_context, program, locals, &ast);

                    let mut stack = crate::interp::Stack::new(2048);

                    let result = crate::interp::interp(program, &mut stack, &routine);

                    program.logger.log(format_args!(
                        "value of '{}' = {}",
                        member_id.to_ustr(),
                        unsafe { *(result as *const u64) }
                    ));

                    program.set_value_of_member(member_id.to_ustr(), result);
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
