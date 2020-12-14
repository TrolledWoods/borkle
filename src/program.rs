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
use std::fmt;
use std::path::{Path, PathBuf};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::Arc;
use ustr::{Ustr, UstrMap};

pub mod constant;
pub mod ffi;
pub mod thread_pool;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct MemberId(usize);

impl fmt::Debug for MemberId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// This is the main hub of the program that is being compiled.
///
/// We deal with constants(and possibly in the future globals too),
/// e.g. data scopes, and the dependency system.
pub struct Program {
    pub arguments: Arguments,

    pub logger: Logger,
    // FIXME: We will have scopes eventually, but for now
    // everything is just in the same scope.
    members: RwLock<HashMap<MemberId, Member>>,
    scope: RwLock<UstrMap<MemberId>>,

    pub constant_data: Mutex<Vec<Constant>>,

    pub libraries: Mutex<ffi::Libraries>,
    pub external_symbols: Mutex<HashMap<*const u8, (Type, Ustr)>>,

    functions: Mutex<HashSet<*const Routine>>,
    calling_conventions_alloc: Mutex<Bump>,
    extern_fn_calling_conventions: RwLock<HashMap<Type, ffi::CallingConvention>>,

    work: thread_pool::WorkPile,

    pub loaded_files: Mutex<HashSet<Ustr>>,
}

// FIXME: Make a wrapper type for *const _ and have Send and Sync for that.
// The thing about the *const _ that I use is that they are truly immutable; and immutable in other
// points, and ALSO they do not allow interior mutability, which means they are threadsafe.
unsafe impl Send for Program {}
unsafe impl Sync for Program {}

impl Program {
    pub fn new(logger: Logger, arguments: Arguments) -> Self {
        Self {
            arguments,

            external_symbols: Mutex::default(),

            logger,

            members: RwLock::default(),
            scope: RwLock::default(),

            extern_fn_calling_conventions: RwLock::default(),
            calling_conventions_alloc: Mutex::default(),
            functions: Mutex::default(),
            libraries: Mutex::new(ffi::Libraries::new()),
            constant_data: Mutex::default(),
            work: thread_pool::WorkPile::new(),

            loaded_files: Mutex::default(),
        }
    }

    pub fn check_for_completion(&self, errors: &mut ErrorCtx) {
        let members = self.members.read();
        for member in members.values() {
            for &(loc, _) in member.type_.dependants() {
                if member.is_defined {
                    errors.error(loc, format!("'{}' can't be evaluated", member.name));
                } else {
                    errors.error(loc, format!("'{}' is not defined", member.name));
                }
            }

            for &(loc, _) in member.value.dependants() {
                if member.is_defined {
                    errors.error(loc, format!("'{}' can't be evaluated", member.name));
                } else {
                    errors.error(loc, format!("'{}' is not defined", member.name));
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
        let members = self.members.read();
        let member_id = self.get_member_id("main".into())?;
        let member = members.get(&member_id).unwrap();

        let type_ = member.type_.to_option()?.0;

        if let TypeKind::Function {
            args,
            returns,
            is_extern: false,
        } = type_.kind()
        {
            if args.is_empty() && matches!(returns.kind(), TypeKind::Int(IntTypeKind::U64)) {
                Some(unsafe { *member.value.to_option()?.as_ptr().cast::<*const u8>() })
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn get_constant_as_value(&self, id: MemberId) -> crate::ir::Value {
        let members = self.members.read();
        let member = members.get(&id).unwrap();

        let type_ = member.type_.to_option().unwrap().0;
        let value_ptr = *member.value.to_option().unwrap();

        crate::ir::Value::Global(value_ptr, type_)
    }

    pub fn get_member_id(&self, name: Ustr) -> Option<MemberId> {
        self.scope.read().get(&name).copied()
    }

    pub fn member_name(&self, id: MemberId) -> Ustr {
        let members = self.members.read();
        members.get(&id).unwrap().name
    }

    pub fn get_value_of_member(&self, id: MemberId) -> ConstantRef {
        let members = self.members.read();
        *members.get(&id).unwrap().value.unwrap()
    }

    pub fn get_member_meta_data(&self, id: MemberId) -> (Type, Arc<MemberMetaData>) {
        let members = self.members.read();
        members.get(&id).unwrap().type_.unwrap().clone()
    }

    pub fn get_type_of_member(&self, id: MemberId) -> Type {
        let members = self.members.read();
        members.get(&id).unwrap().type_.unwrap().0
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

    pub fn add_file(&self, path: impl AsRef<Path>) {
        self.work.enqueue(Task::Parse(path.as_ref().to_path_buf()));
    }

    pub fn insert_buffer_from_operation(
        &self,
        type_: Type,
        get_data: impl FnOnce(*mut u8),
    ) -> ConstantRef {
        if type_.size() == 0 {
            return ConstantRef::dangling();
        }

        let layout = alloc::Layout::from_size_align(type_.size(), type_.align()).unwrap();

        let owned_data = unsafe { alloc::alloc(layout) };
        get_data(owned_data);

        let mut constant_data = self.constant_data.lock();
        let slice_version = unsafe { std::slice::from_raw_parts(owned_data, type_.size()) };
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
            size: type_.size(),
            type_,
        };

        let const_ref = constant.as_ref();
        constant_data.push(constant);

        const_ref
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

    pub fn set_value_of_member(&self, id: MemberId, data: *const u8) {
        let mut members = self.members.write();
        let member = members.get_mut(&id).unwrap();

        let value = self.insert_buffer(member.type_.unwrap().0, data);
        let old = std::mem::replace(&mut member.value, DependableOption::Some(value));

        drop(members);

        if let DependableOption::None(dependencies) = old {
            for (_, dependency) in dependencies {
                self.resolve_dependency(dependency);
            }
        } else {
            unreachable!("You can only set the value of a member once!");
        }
    }

    pub fn set_type_of_member(&self, id: MemberId, type_: Type, meta_data: MemberMetaData) {
        let mut members = self.members.write();
        let member_type = &mut members.get_mut(&id).unwrap().type_;
        let old = std::mem::replace(
            member_type,
            DependableOption::Some((type_, Arc::new(meta_data))),
        );
        drop(members);

        if let DependableOption::None(dependencies) = old {
            for (_, dependency) in dependencies {
                self.resolve_dependency(dependency);
            }
        } else {
            unreachable!("You can only set the type of a member once!");
        }
    }

    fn resolve_dependency(&self, id: MemberId) {
        let name = self.member_name(id);
        let members = self.members.read();
        let dependencies_left = members
            .get(&id)
            .unwrap()
            .dependencies_left
            .fetch_sub(1, Ordering::SeqCst);

        self.logger.log(format_args!(
            "resolved dependency of '{}', had {} deps",
            name, dependencies_left,
        ));

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
            // FIXME: Make more granular locks, don't lock the whole members here.
            drop(members);
            let mut members = self.members.write();
            if let Some(task) = members.get_mut(&id).unwrap().task.take() {
                self.work.enqueue(task);
            } else {
                // There was no task? This shouldn't happen; if there are dependencies,
                // there should be a task.
                unreachable!("Expected there to be a task.");
            }
        }
    }

    pub fn define_member(
        &self,
        errors: &mut ErrorCtx,
        loc: Location,
        name: Ustr,
    ) -> Result<MemberId, ()> {
        let mut scope = self.scope.write();
        let mut members = self.members.write();

        if let Some(&id) = scope.get(&name) {
            let member = members.get_mut(&id).unwrap();
            if member.is_defined {
                errors.error(loc, format!("'{}' is already defined", name));
                return Err(());
            }
            // Here it was already depended upon, so it had a non-defined version, so we just flag
            // it to be defined now.
            member.is_defined = true;
            Ok(id)
        } else {
            let id = MemberId(members.len());
            scope.insert(name, id);
            members.insert(id, Member::new(name, true));
            Ok(id)
        }
    }

    pub fn queue_task(&self, id: MemberId, deps: DependencyList, task: Task) {
        let name = self.member_name(id);

        let mut scope = self.scope.write();
        let mut members = self.members.write();
        let mut num_deps = 0;

        self.logger
            .log(format_args!("queued '{}' {:?}", name, deps));

        // We want to make sure that there are no left over dependencies from the previous task
        // associated with this member.
        debug_assert_eq!(
            members
                .get(&id)
                .unwrap()
                .dependencies_left
                .load(Ordering::SeqCst),
            0
        );

        for (dep_name, loc) in deps.types {
            if let Some(&dep_id) = scope.get(&dep_name) {
                let dependency = members.get_mut(&dep_id).unwrap();
                if dependency.type_.add_dependant(loc, id) {
                    num_deps += 1;
                }
            } else {
                num_deps += 1;
                self.logger.log(format_args!("temporary: '{}'", dep_name,));
                let mut dependency = Member::new(dep_name, false);
                dependency.type_.add_dependant(loc, id);

                let dep_id = MemberId(members.len());
                scope.insert(dep_name, dep_id);
                members.insert(dep_id, dependency);
            }
        }

        for (dep_name, loc) in deps.values {
            if let Some(dep_id) = scope.get(&dep_name) {
                let dependency = members.get_mut(&dep_id).unwrap();
                if dependency.value.add_dependant(loc, id) {
                    num_deps += 1;
                }
            } else {
                num_deps += 1;
                self.logger.log(format_args!("temporary: '{}'", dep_name,));
                let mut dependency = Member::new(dep_name, false);
                dependency.value.add_dependant(loc, id);

                let dep_id = MemberId(members.len());
                scope.insert(dep_name, dep_id);
                members.insert(dep_id, dependency);
            }
        }

        let num_dependencies = members.get_mut(&id).unwrap().dependencies_left.get_mut();

        *num_dependencies += num_deps;

        if *num_dependencies == 0 {
            // We are already done! We can emit the task without
            // doing dependency stuff
            self.work.enqueue(task);
        } else {
            // We are not done with our dependencies. We have to wait a bit,
            // so we have to put the task into the lock.
            let entry = members.get_mut(&id).unwrap();
            entry.task = Some(task);
        }
    }
}

struct Member {
    name: Ustr,
    type_: DependableOption<(Type, Arc<MemberMetaData>)>,
    value: DependableOption<ConstantRef>,
    dependencies_left: AtomicI32,
    task: Option<Task>,
    is_defined: bool,
}

#[derive(Debug)]
pub enum MemberMetaData {
    None,
    Function {
        arg_names: Vec<Ustr>,
        default_values: Vec<ConstantRef>,
    },
}

unsafe impl Send for Member {}
unsafe impl Sync for Member {}

impl Member {
    const fn new(name: Ustr, is_defined: bool) -> Self {
        Self {
            name,
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
    None(Vec<(Location, MemberId)>),
}

impl<T> DependableOption<T> {
    fn add_dependant(&mut self, loc: Location, dependant: MemberId) -> bool {
        match self {
            Self::Some(_) => false,
            Self::None(dependants) => {
                dependants.push((loc, dependant));
                true
            }
        }
    }

    fn dependants(&self) -> &[(Location, MemberId)] {
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

pub enum Task {
    Parse(PathBuf),
    Type(MemberId, crate::locals::LocalVariables, crate::parser::Ast),
    Value(MemberId, crate::locals::LocalVariables, crate::typer::Ast),
}

impl fmt::Debug for Task {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Task::Parse(buf) => write!(f, "parse({:?})", buf),
            Task::Type(id, _, _) => write!(f, "type({:?})", id),
            Task::Value(id, _, _) => write!(f, "value({:?})", id),
        }
    }
}
