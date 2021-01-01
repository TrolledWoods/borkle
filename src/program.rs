use crate::command_line_arguments::Arguments;
use crate::dependencies::{DependencyKind, DependencyList};
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

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeId(usize);

impl fmt::Debug for MemberId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for ScopeId {
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
    pub files: Mutex<UstrMap<String>>,

    pub logger: Logger,
    // FIXME: Make this a vector, not a hashmap you dummy, hashmaps aren't as fast as vectors in
    // this case!?!?!??!?!?!
    members: RwLock<HashMap<MemberId, Member>>,
    scopes: RwLock<Vec<Scope>>,

    pub constant_data: Mutex<Vec<Constant>>,

    pub libraries: Mutex<ffi::Libraries>,
    pub external_symbols: Mutex<HashMap<*const u8, (Type, Ustr)>>,

    functions: Mutex<HashSet<*const Routine>>,
    calling_conventions_alloc: Mutex<Bump>,
    extern_fn_calling_conventions: RwLock<HashMap<Type, ffi::CallingConvention>>,

    work: thread_pool::WorkPile,

    pub loaded_files: Mutex<UstrMap<ScopeId>>,
    pub entry_point: Mutex<Option<MemberId>>,
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
            external_symbols: default(),
            logger,
            members: default(),
            scopes: default(),
            files: default(),
            extern_fn_calling_conventions: RwLock::default(),
            calling_conventions_alloc: Mutex::default(),
            functions: default(),
            libraries: Mutex::new(ffi::Libraries::new()),
            constant_data: default(),
            work: thread_pool::WorkPile::new(),
            loaded_files: default(),
            entry_point: default(),
        }
    }

    pub fn check_for_completion(&self, errors: &mut ErrorCtx) {
        let scopes = self.scopes.read();
        let members = self.members.read();
        for scope in scopes.iter() {
            let wanted_names = scope.wanted_names.read();
            for (&name, dependants) in wanted_names.iter() {
                for &(_, loc, _) in dependants {
                    errors.info(loc, "Dependant here".to_string());
                }
                errors.global_error(format!("'{}' is not defined", name));
            }

            let public_members = scope.public_members.read();
            for (&name, &member_id) in public_members.iter() {
                let member = members.get(&member_id).unwrap();
                if member.type_.to_option().is_none() {
                    errors.global_error(format!("'{}' cannot be computed", name));
                } else if member.value.to_option().is_none() {
                    errors.global_error(format!("'{}' cannot be computed(value)", name));
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
        let member_id = (*self.entry_point.lock())?;
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

    pub fn create_scope(&self) -> ScopeId {
        let mut scopes = self.scopes.write();
        let id = ScopeId(scopes.len());
        scopes.push(Scope {
            public_members: default(),
            private_members: default(),
            wanted_names: default(),
            dependants: default(),
        });
        id
    }

    /// # Fails
    /// When the scopes have conflicting members.
    pub fn add_scope_dependency(
        &self,
        errors: &mut ErrorCtx,
        loc: Location,
        dependant: ScopeId,
        depending_on: ScopeId,
    ) -> Result<(), ()> {
        let scopes = self.scopes.read();
        let mut dependants = scopes[depending_on.0].dependants.write();

        if dependants.contains(&dependant) {
            errors.error(loc, "This is imported twice".to_string());
            return Err(());
        }

        dependants.push(dependant);
        drop(dependants);

        let depending_publics = scopes[depending_on.0].public_members.read();
        for (&name, &member_id) in depending_publics.iter() {
            self.bind_member_to_name(errors, dependant, name, loc, member_id, false)?;
        }

        Ok(())
    }

    pub fn get_member_id(&self, scope: ScopeId, name: Ustr) -> Option<MemberId> {
        let scopes = self.scopes.read();
        let public = scopes[scope.0].public_members.read().get(&name).copied();
        public.or_else(|| scopes[scope.0].private_members.read().get(&name).copied())
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
        self.work
            .enqueue(Task::Parse(None, path.as_ref().to_path_buf()));
    }

    pub fn add_file_from_import(
        &self,
        path: impl AsRef<Path>,
        location: Location,
        from_scope: ScopeId,
    ) {
        self.work.enqueue(Task::Parse(
            Some((location, from_scope)),
            path.as_ref().to_path_buf(),
        ));
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

    pub fn insert_zeroed_buffer(&self, type_: Type) -> ConstantRef {
        if type_.size() == 0 {
            return ConstantRef::dangling();
        }

        let layout = alloc::Layout::from_size_align(type_.size(), 16).unwrap();
        let size = crate::types::to_align(type_.size(), 8);

        let owned_data = unsafe {
            let buffer = alloc::alloc(layout);
            buffer.write_bytes(0, size);
            buffer
        };

        let slice_version = unsafe { std::slice::from_raw_parts(owned_data, size) };
        let mut constant_data = self.constant_data.lock();
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

    pub fn insert_buffer(&self, type_: Type, data: *const u8) -> ConstantRef {
        if type_.size() == 0 {
            return ConstantRef::dangling();
        }

        let layout = alloc::Layout::from_size_align(type_.size(), type_.align()).unwrap();

        let owned_data = unsafe {
            let buffer = alloc::alloc(layout);
            std::ptr::copy(data, buffer, type_.size());
            buffer
        };

        self.insert_sub_buffers(type_, owned_data);

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

    pub fn set_value_of_member(&self, id: MemberId, data: *const u8) {
        let mut members = self.members.write();
        let member = members.get_mut(&id).unwrap();

        let value = self.insert_buffer(member.type_.unwrap().0, data);
        let old = std::mem::replace(&mut member.value, DependableOption::Some(value));

        // This is a zst, we don't need a value.
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
        scope_id: ScopeId,
        name: Ustr,
    ) -> Result<MemberId, ()> {
        let mut members = self.members.write();
        let id = MemberId(members.len());
        members.insert(id, Member::new(name));
        drop(members);

        self.bind_member_to_name(errors, scope_id, name, loc, id, true)?;
        Ok(id)
    }

    fn bind_member_to_name(
        &self,
        errors: &mut ErrorCtx,
        scope_id: ScopeId,
        name: Ustr,
        loc: Location,
        member_id: MemberId,
        is_public: bool,
    ) -> Result<(), ()> {
        let scopes = self.scopes.read();

        let mut public_members = scopes[scope_id.0].public_members.write();
        let mut private_members = scopes[scope_id.0].private_members.write();

        if public_members.contains_key(&name) | private_members.contains_key(&name) {
            errors.error(loc, format!("'{}' is already defined", name));
            return Err(());
        }

        let used_list = if is_public {
            &mut public_members
        } else {
            &mut private_members
        };

        used_list.insert(name, member_id);

        drop(public_members);
        drop(private_members);

        if is_public {
            for dependant in scopes[scope_id.0].dependants.read().iter() {
                self.bind_member_to_name(errors, *dependant, name, loc, member_id, false)?;
            }
        }

        let mut wanted_names = scopes[scope_id.0].wanted_names.write();
        if let Some(dependants) = wanted_names.remove(&name) {
            drop(wanted_names);
            drop(scopes);
            // FIXME: Check if this is congesting it or not.
            for &(kind, _, dependant) in &dependants {
                let dependant_name = self.member_name(dependant);
                let mut members = self.members.write();
                let member = members.get_mut(&member_id).unwrap();
                match kind {
                    DependencyKind::Type => {
                        self.logger.log(format_args!(
                            "'{}' found definition of '{}', now searches for the type of it",
                            dependant_name, member.name,
                        ));

                        if !member.type_.add_dependant(loc, dependant) {
                            drop(members);
                            self.resolve_dependency(dependant);
                        }
                    }
                    DependencyKind::Value => {
                        self.logger.log(format_args!(
                            "'{}' found definition of '{}', now searches for the value of it",
                            dependant_name, member.name,
                        ));

                        if !member.type_.add_dependant(loc, dependant) {
                            drop(members);
                            self.resolve_dependency(dependant);
                        }
                    }
                }
            }
        }

        Ok(())
    }

    pub fn queue_task(&self, id: MemberId, deps: DependencyList, task: Task) {
        let name = self.member_name(id);

        let scopes = self.scopes.read();
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

        for (dep_name, (scope_id, loc)) in deps.types {
            let scope = &scopes[scope_id.0];
            let mut scope_wanted_names = scope.wanted_names.write();

            if let Some(dep_id) = scope.get(dep_name) {
                let dependency = members.get_mut(&dep_id).unwrap();
                if dependency.type_.add_dependant(loc, id) {
                    num_deps += 1;
                }
            } else {
                num_deps += 1;
                self.logger.log(format_args!(
                    "Undefined identifier '{}' in scope {}, wants type of it",
                    dep_name, scope_id.0
                ));
                let wanted = scope_wanted_names.entry(dep_name).or_insert_with(Vec::new);
                wanted.push((DependencyKind::Type, loc, id));
            }
        }

        for (dep_name, (scope_id, loc)) in deps.values {
            let scope = &scopes[scope_id.0];
            let mut scope_wanted_names = scope.wanted_names.write();

            if let Some(dep_id) = scope.get(dep_name) {
                let dependency = members.get_mut(&dep_id).unwrap();
                if dependency.value.add_dependant(loc, id) {
                    num_deps += 1;
                }
            } else {
                num_deps += 1;
                self.logger.log(format_args!(
                    "Undefined identifier '{}' in scope {}, wants value of it",
                    dep_name, scope_id.0
                ));
                let wanted = scope_wanted_names.entry(dep_name).or_insert_with(Vec::new);
                wanted.push((DependencyKind::Value, loc, id));
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

struct Scope {
    // FIXME: Have these store the location where the thing was bound to a name as well.
    // At least in the public_members, since those are usually not imported but bound in the scope?
    // However, even private_members would have a use for the location of the import/library
    public_members: RwLock<UstrMap<MemberId>>,
    private_members: RwLock<UstrMap<MemberId>>,
    wanted_names: RwLock<UstrMap<Vec<(DependencyKind, Location, MemberId)>>>,
    dependants: RwLock<Vec<ScopeId>>,
}

impl Scope {
    fn get(&self, name: Ustr) -> Option<MemberId> {
        let public = self.public_members.read().get(&name).copied();
        public.or_else(|| self.private_members.read().get(&name).copied())
    }
}

struct Member {
    name: Ustr,
    type_: DependableOption<(Type, Arc<MemberMetaData>)>,
    value: DependableOption<ConstantRef>,
    dependencies_left: AtomicI32,
    task: Option<Task>,
}

#[derive(Debug, Clone)]
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
    const fn new(name: Ustr) -> Self {
        Self {
            name,
            type_: DependableOption::None(Vec::new()),
            value: DependableOption::None(Vec::new()),
            dependencies_left: AtomicI32::new(0),
            task: None,
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
    Parse(Option<(Location, ScopeId)>, PathBuf),
    Type(MemberId, crate::locals::LocalVariables, crate::parser::Ast),
    Value(MemberId, crate::locals::LocalVariables, crate::typer::Ast),
}

impl fmt::Debug for Task {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Task::Parse(_, buf) => write!(f, "parse({:?})", buf),
            Task::Type(id, _, _) => write!(f, "type({:?})", id),
            Task::Value(id, _, _) => write!(f, "value({:?})", id),
        }
    }
}

fn default<T: Default>() -> T {
    T::default()
}
