use crate::dependencies::DependencyList;
use crate::thread_pool::WorkSender;
use crate::types::Type;
use parking_lot::RwLock;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};
use ustr::{Ustr, UstrMap};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct MemberId(Ustr);

impl MemberId {
    // Temporary function, will be removed once scopes are added.
    pub const fn from_ustr(ustr: Ustr) -> Self {
        Self(ustr)
    }
}

/// This is the main hub of the program that is being compiled.
///
/// We deal with constants(and possibly in the future globals too),
/// e.g. data scopes, and the dependency system.
pub struct Program {
    // TODO: We will have scopes eventually, but for now
    // everything is just in the same scope.
    const_table: RwLock<UstrMap<Member>>,
    work: WorkSender,
}

impl Program {
    pub fn new(work: WorkSender) -> Self {
        Self {
            const_table: RwLock::default(),
            work,
        }
    }

    pub fn get_type_of_member(&self, id: Ustr) -> Option<Type> {
        let const_table = self.const_table.read();
        const_table.get(&id).unwrap().type_.to_option().copied()
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
            self.work.send(task);
        } else {
            // We are not done with our dependencies. We have to wait a bit,
            // so we have to put the task into the lock.
            const_table.get_mut(&name).unwrap().task = Some(task);
        }
    }
}

struct Member {
    type_: DependableOption<Type>,
    value: DependableOption<Vec<u8>>,
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

    const fn to_option(&self) -> Option<&T> {
        match self {
            Self::Some(value) => Some(value),
            Self::None(_) => None,
        }
    }
}

#[derive(Debug)]
pub enum Task {
    Parse(Ustr, PathBuf),
    Type(crate::locals::LocalVariables, crate::parser::Ast),
    Value(crate::locals::LocalVariables, crate::typer::Ast),
}
