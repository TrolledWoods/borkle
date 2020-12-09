use crate::command_line_arguments::Arguments;
use crate::dependencies::DependencyList;
use crate::errors::ErrorCtx;
use crate::ir::Routine;
use crate::location::Location;
use crate::logging::Logger;
use crate::types::{IntTypeKind, PointerInType, Type, TypeKind};
use bumpalo::Bump;
use constant::{Constant, ConstantRef};
use parking_lot::{Mutex, RwLock};
use std::alloc;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicI32, Ordering};
use thread_pool::WorkSender;
use ustr::{Ustr, UstrMap};

pub mod constant;
pub mod ffi;
pub mod thread_pool;

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
    pub arguments: Box<Arguments>,

    pub logger: Logger,
    // FIXME: We will have scopes eventually, but for now
    // everything is just in the same scope.
    // FIXME: Fix up the terminology here, 'Constant' vs 'StaticData' maybe? Instaed of
    // 'const_table', 'member'?, 'constant_data'.
    const_table: RwLock<UstrMap<Member>>,
    pub constant_data: Mutex<Vec<Constant>>,

    pub libraries: Mutex<ffi::Libraries>,
    pub external_symbols: Mutex<HashMap<*const u8, (Type, Ustr)>>,

    functions: Mutex<HashSet<*const Routine>>,
    calling_conventions_alloc: Mutex<Bump>,
    extern_fn_calling_conventions: RwLock<HashMap<Type, ffi::CallingConvention>>,

    // This has to live for as long as the interpreter runs, because, we have no idea
    // how long the pointers to functions might live inside of the compile time execution things,
    // so we have to just have them all alive for the entire duration of the program.
    work: WorkSender,

    pub loaded_files: Mutex<HashSet<Ustr>>,
}

// FIXME: Make a wrapper type for *const _ and have Send and Sync for that.
// The thing about the *const _ that I use is that they are truly immutable; and immutable in other
// points, and ALSO they do not allow interior mutability, which means they are threadsafe.
unsafe impl Send for Program {}
unsafe impl Sync for Program {}

impl Program {
    pub fn new(logger: Logger, work: WorkSender, options: Box<Arguments>) -> Self {
        Self {
            arguments: options,

            external_symbols: Mutex::default(),

            logger,
            const_table: RwLock::default(),
            extern_fn_calling_conventions: RwLock::default(),
            calling_conventions_alloc: Mutex::default(),
            functions: Mutex::default(),
            libraries: Mutex::new(ffi::Libraries::new()),
            constant_data: Mutex::default(),
            work,

            loaded_files: Mutex::default(),
        }
    }

    pub fn check_for_completion(&self, errors: &mut ErrorCtx) {
        let const_table = self.const_table.read();
        for (name, constant) in const_table.iter() {
            for &(loc, _) in constant.type_.dependants() {
                if constant.is_defined {
                    errors.error(loc, format!("'{}' can't be evaluated", name));
                } else {
                    errors.error(loc, format!("'{}' is not defined", name));
                }
            }

            for &(loc, _) in constant.value.dependants() {
                if constant.is_defined {
                    errors.error(loc, format!("'{}' can't be evaluated", name));
                } else {
                    errors.error(loc, format!("'{}' is not defined", name));
                }
            }
        }
    }

    pub fn insert_function(&self, routine: Routine) -> usize {
        let mut functions = self.functions.lock();
        let leaked = Box::leak(Box::new(routine)) as *const Routine;
        functions.insert(leaked);
        leaked as usize
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

    pub fn get_entry_point(&self) -> Option<*const u8> {
        let const_table = self.const_table.read();
        let element = const_table.get(&"main".into())?;

        let type_ = element.type_.to_option()?;

        if let TypeKind::Function {
            args,
            returns,
            is_extern: false,
        } = type_.kind()
        {
            if args.is_empty() && matches!(returns.kind(), TypeKind::Int(IntTypeKind::U64)) {
                Some(unsafe { *element.value.to_option()?.as_ptr().cast::<*const u8>() })
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn get_constant_as_value(&self, id: MemberId) -> crate::ir::Value {
        let const_table = self.const_table.read();
        let element = const_table.get(&id.0).unwrap();

        let type_ = *element.type_.to_option().unwrap();
        let value_ptr = *element.value.to_option().unwrap();

        crate::ir::Value::Global(value_ptr, type_)
    }

    pub fn get_type_of_member(&self, id: Ustr) -> Option<Type> {
        let const_table = self.const_table.read();
        const_table.get(&id).unwrap().type_.to_option().copied()
    }

    pub fn load_extern_library(
        &self,
        library_name: &Path,
        symbol_name: Ustr,
        type_: Type,
    ) -> Result<unsafe extern "C" fn(), libloading::Error> {
        let mut libraries = self.libraries.lock();
        let mut external_symbols = self.external_symbols.lock();
        let func = libraries.load_symbol(library_name, symbol_name.as_str().into())?;
        external_symbols.insert(func as *const u8, (type_, symbol_name));
        Ok(func)
    }

    fn insert_sub_buffers(&self, type_: Type, data: *mut u8) {
        for (offset, ptr) in type_.pointers() {
            match ptr {
                PointerInType::Pointer(internal) => unsafe {
                    let sub_buffer =
                        self.insert_buffer(*internal, *data.add(*offset).cast::<*const u8>());
                    *data.cast::<*const u8>() = sub_buffer.as_ptr();
                },
                PointerInType::Buffer(internal) => {
                    let buffer = unsafe { &mut *data.cast::<crate::types::BufferRepr>() };

                    if buffer.length != 0 {
                        let array_type = Type::new(TypeKind::Array(*internal, buffer.length));
                        let sub_buffer = self.insert_buffer(array_type, buffer.ptr);

                        buffer.ptr = sub_buffer.as_ptr() as *mut _;
                    } else {
                        buffer.ptr = std::ptr::null_mut();
                    }
                }
                PointerInType::Function { .. } => {}
            }
        }
    }

    pub fn add_file(&self, path: PathBuf) {
        self.work.send(Task::Parse(path));
    }

    pub fn insert_buffer(&self, type_: Type, data: *const u8) -> ConstantRef {
        if type_.size() == 0 {
            return ConstantRef::dangling();
        }

        let layout = alloc::Layout::from_size_align(type_.size(), 16).unwrap();
        let size = crate::types::to_align(type_.size(), 8);

        let owned_data = unsafe {
            // The alignment of the buffer is '16' here, no matter what the type is, because
            // different types of constants might have the same memory in static memory,
            // but their alignment might be different, so it's better to be safe here than sorry.
            let buffer = alloc::alloc(layout);
            std::ptr::copy(data, buffer, type_.size());
            buffer.add(type_.size()).write_bytes(0, size - type_.size());
            buffer
        };

        self.insert_sub_buffers(type_, owned_data);

        let mut constant_data = self.constant_data.lock();

        let slice_version = unsafe { std::slice::from_raw_parts(owned_data, size) };
        for pre_computed_constant in constant_data.iter() {
            if pre_computed_constant.type_ == type_
                && pre_computed_constant.as_slice() == slice_version
            {
                unsafe {
                    alloc::dealloc(owned_data, layout);
                }
                return pre_computed_constant.as_ref();
            }
        }

        let constant = Constant {
            ptr: NonNull::new(owned_data).unwrap(),
            size,
            type_,
        };

        let const_ref = constant.as_ref();
        constant_data.push(constant);

        const_ref
    }

    pub fn set_value_of_member(&self, id: Ustr, data: *const u8) {
        let mut const_table = self.const_table.write();
        let entry = const_table.get_mut(&id).unwrap();

        let value = self.insert_buffer(*entry.type_.unwrap(), data);
        let old = std::mem::replace(&mut entry.value, DependableOption::Some(value));

        drop(const_table);

        if let DependableOption::None(dependencies) = old {
            for (_, dependency) in dependencies {
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
            for (_, dependency) in dependencies {
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
    /// FIXME: Once we separate program and tasks, we probably want to move this into the task
    /// system, and not have it here. But that might not be desirable.
    pub fn insert(
        &self,
        errors: &mut ErrorCtx,
        loc: Location,
        name: Ustr,
        deps: DependencyList,
        expect_it_is_new_thing: bool,
        task: impl FnOnce(MemberId) -> Task,
    ) -> Result<(), ()> {
        let mut const_table = self.const_table.write();

        let mut num_deps = 0;
        if const_table.contains_key(&name) {
            let member = const_table.get_mut(&name).unwrap();
            if member.is_defined && expect_it_is_new_thing {
                errors.error(loc, format!("'{}' is already defined", name));
                return Err(());
            }
            member.is_defined = true;
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

        for (dependency, loc) in deps.values {
            if let Some(member) = const_table.get_mut(&dependency) {
                if member.value.add_dependant(loc, name) {
                    num_deps += 1;
                }
            } else {
                num_deps += 1;
                self.logger.log(format_args!(
                    "Temporary member '{}' added for dependency resolution",
                    dependency
                ));
                let mut member = Member::new(false);
                member.value.add_dependant(loc, name);
                const_table.insert(dependency, member);
            }
        }

        for (dependency, loc) in deps.types {
            if let Some(member) = const_table.get_mut(&dependency) {
                if member.value.add_dependant(loc, name) {
                    num_deps += 1;
                }
            } else {
                num_deps += 1;
                self.logger.log(format_args!(
                    "Temporary member '{}' added for dependency resolution",
                    dependency
                ));
                let mut member = Member::new(false);
                member.type_.add_dependant(loc, name);
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

        Ok(())
    }
}

struct Member {
    type_: DependableOption<Type>,
    value: DependableOption<ConstantRef>,
    dependencies_left: AtomicI32,
    task: Option<Task>,
    is_defined: bool,
}

unsafe impl Send for Member {}
unsafe impl Sync for Member {}

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
    None(Vec<(Location, Ustr)>),
}

impl<T> DependableOption<T> {
    fn add_dependant(&mut self, loc: Location, dependant: Ustr) -> bool {
        match self {
            Self::Some(_) => false,
            Self::None(dependants) => {
                dependants.push((loc, dependant));
                true
            }
        }
    }

    fn dependants(&self) -> &[(Location, Ustr)] {
        match self {
            Self::Some(_) => &[],
            Self::None(dependants) => dependants,
        }
    }

    pub fn unwrap(&self) -> &T {
        self.to_option().unwrap()
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
    Parse(PathBuf),
    Type(MemberId, crate::locals::LocalVariables, crate::parser::Ast),
    Value(MemberId, crate::locals::LocalVariables, crate::typer::Ast),
}
