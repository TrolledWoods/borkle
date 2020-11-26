use crate::dependencies::DependencyList;
use crate::thread_pool::WorkSender;
use crate::types::Type;
use bumpalo::Bump;
use parking_lot::{Mutex, RwLock};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::atomic::{AtomicI32, Ordering};
use ustr::{Ustr, UstrMap};

pub mod ffi;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct MemberId(Ustr);

impl MemberId {
    // Temporary function, will be removed once scopes are added.
    pub const fn from_ustr(ustr: Ustr) -> Self {
        Self(ustr)
    }

    // Temporary function, will be removed once scopes are added.
    pub const fn to_ustr(self) -> Ustr {
        self.0
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
    calling_conventions_alloc: Mutex<Bump>,
    extern_fn_calling_conventions: RwLock<HashMap<Type, ffi::CallingConvention>>,
    work: WorkSender,
    pub libraries: Mutex<ffi::Libraries>,
}

impl Program {
    pub fn new(work: WorkSender) -> Self {
        Self {
            const_table: RwLock::default(),
            extern_fn_calling_conventions: RwLock::default(),
            calling_conventions_alloc: Mutex::default(),
            libraries: Mutex::new(ffi::Libraries::new()),
            work,
        }
    }

    pub fn ffi_calling_convention(&self, function_type: Type) -> ffi::CallingConvention {
        let guard = self.extern_fn_calling_conventions.read();
        if let Some(convention) = guard.get(&function_type).copied() {
            convention
        } else {
            drop(guard);
            let mut guard = self.extern_fn_calling_conventions.write();
            let alloc = self.calling_conventions_alloc.lock();
            let convention = ffi::CallingConvention::new(&alloc, function_type);
            guard.insert(function_type, convention);
            convention
        }
    }

    pub fn copy_value_into_slice(&self, id: MemberId, slice: &mut [u8]) {
        let const_table = self.const_table.read();
        if let DependableOption::Some(value) = &const_table.get(&id.0).unwrap().value {
            slice.copy_from_slice(value);
        } else {
            panic!("Can't call copy_value_into_slice if you aren't sure the value is defined");
        }
    }

    pub fn get_type_of_member(&self, id: Ustr) -> Option<Type> {
        let const_table = self.const_table.read();
        const_table.get(&id).unwrap().type_.to_option().copied()
    }

    pub fn set_value_of_member(&self, id: Ustr, value: Vec<u8>) {
        let mut const_table = self.const_table.write();
        let value_entry = &mut const_table.get_mut(&id).unwrap().value;
        let old = std::mem::replace(value_entry, DependableOption::Some(value));
        drop(const_table);

        if let DependableOption::None(dependencies) = old {
            for dependency in dependencies {
                self.resolve_dependency(dependency);
            }
        } else {
            unreachable!("You can only set the value of a member once!");
        }
    }

    pub fn set_type_of_member(&self, id: Ustr, type_: Type) {
        let mut const_table = self.const_table.write();
        let type_entry = &mut const_table.get_mut(&id).unwrap().type_;
        let old = std::mem::replace(type_entry, DependableOption::Some(type_));
        drop(const_table);

        if let DependableOption::None(dependencies) = old {
            for dependency in dependencies {
                self.resolve_dependency(dependency);
            }
        } else {
            unreachable!("You can only set the type of a member once!");
        }
    }

    fn resolve_dependency(&self, id: Ustr) {
        let const_table = self.const_table.read();
        let dependencies_left = const_table
            .get(&id)
            .unwrap()
            .dependencies_left
            .fetch_sub(1, Ordering::SeqCst);

        // This is not a data race. The reason why is a little complicated.
        // So, when dependencies are added, they are added first, and only afterwards
        // is the counter increased all at once.
        //
        // We only add more dependencies once all the previous dependencies have resolved;
        // i.e, while we are adding more dependencies, the dependency count is at 0. That means
        // that if dependencies added are resolved before all of them have finished being added,
        // they will reduce the counter to something negative; which means it will not be 1.
        //
        // If the counter is indeed one(i.e. it was decremented to zero), here is the ONLY case
        // where that would happen; this is the only dependency left, and, there is no dependency
        // currently being added(because the dependencies_left was larger than zero). Therefore,
        // there is going to be no contending over the lock here.
        //
        // This is currently not being done at all though; because we are doing some unnecessarily
        // libral locking. But in the future, we can reduce the amount of locking being done and
        // therefore all of this will become relevant and important.
        if dependencies_left == 1 {
            // FIXME: Make more granular locks, don't lock the whole const_table here.
            drop(const_table);
            let mut const_table = self.const_table.write();
            if let Some(task) = const_table.get_mut(&id).unwrap().task.take() {
                self.work.send(task);
            } else {
                // There was no task? This shouldn't happen; if there are dependencies,
                // there should be a task.
                unreachable!("Expected there to be a task.");
            }
        }
    }

    /// Inserts an element, such that after all the dependencies are resolved
    /// the task will be run.
    ///
    /// FIXME: The 'impl' here will increase code size; we should break this into 2 functions, one
    /// that just constructs the task and another that actually does the inserting.
    pub fn insert(&self, name: Ustr, deps: DependencyList, task: impl FnOnce(MemberId) -> Task) {
        let mut const_table = self.const_table.write();

        let mut num_deps = 0;
        if const_table.contains_key(&name) {
            const_table.get_mut(&name).unwrap().is_defined = true;
        } else {
            // There is some subtelty here that is quite important;
            // we do not insert the task yet. That is because otherwise,
            // the task might be run before we have inserted all the necessary
            // dependencies, and that would mean that the task would run
            // without all the dependencies resolved.
            const_table.insert(name, Member::new(true));
        }

        assert_eq!(
            const_table
                .get(&name)
                .unwrap()
                .dependencies_left
                .load(Ordering::SeqCst),
            0
        );

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
            self.work.send(task(MemberId(name)));
        } else {
            // We are not done with our dependencies. We have to wait a bit,
            // so we have to put the task into the lock.
            let entry = const_table.get_mut(&name).unwrap();
            entry.task = Some(task(MemberId(name)));
        }
    }
}

struct Member {
    type_: DependableOption<Type>,
    value: DependableOption<Vec<u8>>,
    dependencies_left: AtomicI32,
    task: Option<Task>,
    is_defined: bool,
}

impl Member {
    const fn new(is_defined: bool) -> Self {
        Self {
            type_: DependableOption::None(Vec::new()),
            value: DependableOption::None(Vec::new()),
            dependencies_left: AtomicI32::new(0),
            task: None,
            is_defined,
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
    Type(MemberId, crate::locals::LocalVariables, crate::parser::Ast),
    Value(MemberId, crate::locals::LocalVariables, crate::typer::Ast),
}
