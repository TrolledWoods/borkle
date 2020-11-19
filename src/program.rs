use crate::dependencies::DependencyList;
use parking_lot::{Mutex, RwLock};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};
use ustr::{Ustr, UstrMap};

/// This is the main hub of the program that is being compiled.
///
/// We deal with constants(and possibly in the future globals too),
/// e.g. data scopes, and the dependency system.
#[derive(Default)]
pub struct Program {
    // TODO: We will have scopes eventually, but for now
    // everything is just in the same scope.
    const_table: RwLock<UstrMap<Member>>,
}

impl Program {
    pub fn new() -> Self {
        Self::default()
    }

    /// Inserts an element, such that after all the dependencies are resolved
    /// the task will be run.
    pub fn insert(&self, name: Ustr, deps: DependencyList, task: Task) {
        let mut const_table = self.const_table.write();

        let mut num_deps = 0;
        if !const_table.contains_key(&name) {
            // There is some subtelty here that is quite important;
            // we do not insert the task yet. That is because otherwise,
            // the task might be run before we have inserted all the necessary
            // dependencies, and that would mean that the task would run
            // without all the dependencies resolved.
            const_table.insert(name, Member::new(true));
        }

        for dependency in deps.values {
            if let Some(member) = const_table.get_mut(&dependency) {
                if member.value.add_dependant(name) {
                    num_deps += 1;
                }
            } else {
                num_deps += 1;
                let mut member = Member::new(false);
                member.value.add_dependant(name);
                const_table.insert(dependency, member);
            }
        }

        for dependency in deps.types {
            if let Some(member) = const_table.get_mut(&dependency) {
                if member.value.add_dependant(name) {
                    num_deps += 1;
                }
            } else {
                num_deps += 1;
                let mut member = Member::new(false);
                member.type_.add_dependant(name);
                const_table.insert(dependency, member);
            }
        }

        let num_dependencies = const_table
            .get_mut(&name)
            .unwrap()
            .dependencies_left
            .get_mut();

        *num_dependencies += num_deps;

        if *num_dependencies == 0 {
            // We are already done! We can emit the task without
            // doing dependency stuff
            println!("Emit the task {:?}", task);
        } else {
            // We are not done with our dependencies. We have to wait a bit,
            // so we have to put the task into the lock.
            const_table.get_mut(&name).unwrap().task = Some(task);
        }
    }
}

struct Member {
    type_: DependableOption<()>,
    value: DependableOption<()>,
    dependencies_left: AtomicU32,
    task: Option<Task>,
    is_defined: bool,
}

impl Member {
    const fn new(is_defined: bool) -> Self {
        Self {
            type_: DependableOption::None(Vec::new()),
            value: DependableOption::None(Vec::new()),
            dependencies_left: AtomicU32::new(0),
            task: None,
            is_defined,
        }
    }

    fn resolve_dependency(&mut self) {
        let old = self.dependencies_left.fetch_sub(1, Ordering::Relaxed);
        if old == 1 {
            // All dependencies are resolved!
            // If there is a task here, put it on the queue!
            if let Some(task) = self.task.take() {
                println!("TODO: Queue task {:?}", task);
            }
        }
    }
}

pub enum DependableOption<T> {
    Some(T),
    None(Vec<Ustr>),
}

impl<T> DependableOption<T> {
    fn add_dependant(&mut self, dependant: Ustr) -> bool {
        match self {
            Self::Some(_) => false,
            Self::None(dependants) => {
                dependants.push(dependant);
                true
            }
        }
    }
}

#[derive(Debug)]
pub enum Task {
    Parse(Ustr, PathBuf),
    Type(crate::parser::Ast),
}
