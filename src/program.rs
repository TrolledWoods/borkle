use crate::command_line_arguments::Arguments;
use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::id::{Id, IdVec};
use crate::ir::Routine;
use crate::location::Location;
use crate::logging::Logger;
use crate::thread_pool::WorkPile;
use crate::types::{IntTypeKind, PointerInType, Type, TypeKind};
use constant::{Constant, ConstantRef};
use parking_lot::{Mutex, RwLock};
use std::alloc;
use std::collections::HashSet;
use std::fmt;
use std::path::{Path, PathBuf};
use std::ptr::NonNull;
use std::sync::Arc;
use ustr::{Ustr, UstrMap};

pub mod constant;

/// This is the main hub of the program that is being compiled.
///
/// We deal with constants(and possibly in the future globals too),
/// e.g. data scopes, and the dependency system.
///
/// This struct also makes sure that locking happens correctly and doesn't jam or cause race
/// conditions; calling any function on this program at any time should be fine from the rest
/// of the program(from a threading perspective, not from a correctness perspective, i.e. if you
/// pass it garbage it doesn't expect naturally that would cause problems, like passing an invalid
/// pointer to ``insert_buffer`` while the type isn't a zst for example)!
pub struct Program {
    pub arguments: Arguments,
    pub logger: Logger,

    members: RwLock<IdVec<MemberId, Member>>,
    scopes: RwLock<IdVec<ScopeId, Scope>>,

    constant_data: Mutex<Vec<Constant>>,

    functions: RwLock<IdVec<FunctionId, Function>>,
    non_ready_tasks: Mutex<Vec<(u32, Option<NonReadyTask>)>>,

    work: WorkPile,

    // FIXME: This shouldn't be public, but is for now so that the thread pool can do things with
    // it.
    pub loaded_files: Mutex<UstrMap<ScopeId>>,
    pub entry_point: Mutex<Option<MemberId>>,
    file_contents: Mutex<UstrMap<String>>,
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
            logger,
            members: default(),
            scopes: default(),
            non_ready_tasks: default(),
            file_contents: default(),
            functions: default(),
            constant_data: default(),
            work: WorkPile::new(),
            loaded_files: default(),
            entry_point: default(),
        }
    }

    pub fn file_contents(&mut self) -> &mut UstrMap<String> {
        self.file_contents.get_mut()
    }

    pub fn constant_data(&mut self) -> &mut Vec<Constant> {
        self.constant_data.get_mut()
    }

    pub fn work(&self) -> &WorkPile {
        &self.work
    }

    pub fn check_for_completion(&mut self, errors: &mut ErrorCtx) {
        let scopes = self.scopes.get_mut();
        let members = self.members.get_mut();
        for scope in scopes.iter_mut() {
            let wanted_names = scope.wanted_names.get_mut();
            for (&name, dependants) in wanted_names.iter() {
                for &(_, loc, _) in dependants {
                    errors.info(loc, "Dependant here".to_string());
                }
                errors.global_error(format!("'{}' is not defined", name));
            }

            for (&name, &member_id) in &scope.public_members {
                let member = &members[member_id];
                if member.type_.to_option().is_none() {
                    errors.global_error(format!("'{}' cannot be computed", name));
                } else if member.value.to_option().is_none() {
                    errors.global_error(format!("'{}' cannot be computed(value)", name));
                }
            }
        }
    }

    /// Locks
    /// * ``functions`` write
    pub fn insert_defined_function(
        &self,
        loc: Location,
        calls: Vec<FunctionId>,
        routine: Routine,
    ) -> FunctionId {
        let mut functions = self.functions.write();
        functions.push(Function {
            loc,
            routine: DependableOption::Some((calls, Arc::new(routine))),
            dependants: Some(default()),
        })
    }

    /// Locks
    /// * ``functions`` write
    pub fn insert_function(&self, loc: Location) -> FunctionId {
        let mut functions = self.functions.write();
        functions.push(Function {
            loc,
            routine: DependableOption::None(default()),
            dependants: Some(default()),
        })
    }

    /// Locks
    /// * ``functions`` write
    /// * ``non_ready_tasks`` write
    pub fn set_routine_of_function(
        &self,
        function_id: FunctionId,
        calling: Vec<FunctionId>,
        routine: Routine,
    ) {
        let mut functions = self.functions.write();
        let old = std::mem::replace(
            &mut functions[function_id].routine,
            DependableOption::Some((calling, Arc::new(routine))),
        );
        drop(functions);

        if let DependableOption::None(dependants) = old {
            for (loc, dependant) in dependants.into_inner() {
                let functions = self.functions.read();
                let mut num_deps = -1;

                for &calling in &functions[function_id].routine.unwrap().0 {
                    insert_callable_dependency_recursive(
                        &functions,
                        calling,
                        loc,
                        dependant,
                        &mut num_deps,
                    );
                }
                drop(functions);

                self.modify_dependency_count(dependant, num_deps);
            }
        } else {
            unreachable!("This should not happen bro");
        }
    }

    /// Locks
    /// * ``functions`` read
    pub fn get_routine(&self, id: FunctionId) -> Option<Arc<Routine>> {
        let functions = self.functions.read();

        // FIXME: This is not very good for performance, we want to avoid cloning arcs. Could we
        // have an unsafe version of get_routine that makes assumptions?
        functions[id]
            .routine
            .to_option()
            .map(|(_, x)| Arc::clone(x))
    }

    /// Locks
    /// * ``entry_point`` write
    /// * ``members`` read
    pub fn get_entry_point(&self) -> Option<FunctionId> {
        let member_id = (*self.entry_point.lock())?;

        let members = self.members.read();
        let member = &members[member_id];

        let type_ = member.type_.to_option()?.0;

        if let TypeKind::Function { args, returns } = type_.kind() {
            if args.is_empty() && matches!(returns.kind(), TypeKind::Int(IntTypeKind::U64)) {
                Some(unsafe { *member.value.to_option()?.as_ptr().cast::<FunctionId>() })
            } else {
                None
            }
        } else {
            None
        }
    }

    /// # Locks
    /// * ``members`` read
    pub fn get_constant_as_value(&self, id: MemberId) -> crate::ir::Value {
        let (ptr, type_) = self.get_member_value(id);
        crate::ir::Value::Global(ptr, type_)
    }

    /// # Locks
    /// * ``members`` read
    pub fn get_member_value(&self, id: MemberId) -> (ConstantRef, Type) {
        let members = self.members.read();
        let member = &members[id];

        let type_ = member.type_.to_option().unwrap().0;
        let value_ptr = *member.value.to_option().unwrap();

        (value_ptr, type_)
    }

    /// # Locks
    /// * ``scopes`` write
    pub fn create_scope(&self) -> ScopeId {
        self.scopes.write().push(default())
    }

    /// # Fails
    /// When the scopes have conflicting members.
    pub fn insert_wildcard_export(
        &self,
        errors: &mut ErrorCtx,
        loc: Location,
        from: ScopeId,
        to: ScopeId,
    ) -> Result<(), ()> {
        let scopes = self.scopes.read();
        let mut wildcards = scopes[from].wildcard_exports.write();

        if wildcards.contains(&to) {
            errors.error(loc, "This is imported twice".to_string());
            return Err(());
        }

        wildcards.push(to);
        // FIXME: I don't really know how to fix this performance wise without messing up the
        // locks.
        let public_members = scopes[from].public_members.clone();
        drop(wildcards);
        drop(scopes);

        for (name, member_id) in public_members {
            self.bind_member_to_name(errors, to, name, loc, member_id, false)?;
        }

        Ok(())
    }

    /// Locks
    /// * ``scopes`` read
    pub fn get_member_id(&self, scope: ScopeId, name: Ustr) -> Option<MemberId> {
        let scopes = self.scopes.read();
        let public = scopes[scope].public_members.get(&name).copied();
        public.or_else(|| scopes[scope].private_members.get(&name).copied())
    }

    /// Locks
    /// * ``members`` read
    pub fn member_name(&self, id: MemberId) -> Ustr {
        let members = self.members.read();
        members[id].name
    }

    /// Locks
    /// * ``members`` read
    pub fn get_value_of_member(&self, id: MemberId) -> ConstantRef {
        let members = self.members.read();
        *members[id].value.unwrap()
    }

    /// Locks
    /// * ``members`` read
    pub fn get_member_meta_data(&self, id: MemberId) -> (Type, Arc<MemberMetaData>) {
        let members = self.members.read();
        members[id].type_.unwrap().clone()
    }

    /// Locks
    /// * ``constant_data`` write
    fn insert_sub_buffers(&self, type_: Type, data: *mut u8) {
        for (offset, ptr) in type_.pointers() {
            match ptr {
                PointerInType::Pointer(internal) => unsafe {
                    let ptr = *data.add(*offset).cast::<*const u8>();
                    if !ptr.is_null() {
                        let sub_buffer = self.insert_buffer(*internal, ptr);
                        *data.cast::<*const u8>() = sub_buffer.as_ptr();
                    }
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

    /// Locks
    /// * ``files`` write
    pub fn insert_file_contents(&self, name: Ustr, path: String) {
        self.file_contents.lock().insert(name, path);
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

    /// Locks
    /// * ``constant_data`` write
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
            type_,
        };

        let const_ref = constant.as_ref();
        constant_data.push(constant);

        const_ref
    }

    /// # Locks
    /// * ``constant_data`` write
    pub fn insert_zeroed_buffer(&self, type_: Type) -> ConstantRef {
        self.insert_buffer_from_operation(type_, |buf| unsafe { buf.write_bytes(0, type_.size()) })
    }

    /// # Locks
    /// * ``constant_data`` write
    pub fn insert_buffer(&self, type_: Type, data: *const u8) -> ConstantRef {
        self.insert_buffer_from_operation(type_, |buf| unsafe {
            std::ptr::copy(data, buf, type_.size())
        })
    }

    pub fn flag_member_callable(&self, id: MemberId) {
        let mut members = self.members.write();
        let old = std::mem::replace(&mut members[id].callable, DependableOption::Some(()));
        drop(members);

        if let DependableOption::None(dependencies) = old {
            for (_, dependency) in dependencies.into_inner() {
                self.resolve_dependency(dependency);
            }
        }
    }

    /// # Locks
    /// * ``constant_data`` write
    /// * ``members`` write
    /// * ``functions`` write
    pub fn set_value_of_member(&self, id: MemberId, data: *const u8) {
        let type_ = self.members.write()[id].type_.unwrap().0;

        let value = self.insert_buffer(type_, data);

        let mut members = self.members.write();
        let old = std::mem::replace(&mut members[id].value, DependableOption::Some(value));
        drop(members);

        if let DependableOption::None(dependencies) = old {
            for (_, dependency) in dependencies.into_inner() {
                self.resolve_dependency(dependency);
            }
        } else {
            unreachable!("You can only set the value of a member once!");
        }
    }

    /// # Locks
    /// * ``members`` write
    pub fn set_type_of_member(&self, id: MemberId, type_: Type, meta_data: MemberMetaData) {
        let mut members = self.members.write();
        let member_type = &mut members[id].type_;
        let old = std::mem::replace(
            member_type,
            DependableOption::Some((type_, Arc::new(meta_data))),
        );
        drop(members);

        if let DependableOption::None(dependencies) = old {
            for (_, dependency) in dependencies.into_inner() {
                self.resolve_dependency(dependency);
            }
        } else {
            unreachable!("You can only set the type of a member once!");
        }
    }

    /// # Locks
    /// Locks ``non_ready_tasks`` with write.
    fn modify_dependency_count(&self, id: TaskId, offset: i32) {
        if offset == 0 {
            return;
        }

        let mut tasks = self.non_ready_tasks.lock();

        let mut task = {
            let (gen, task_option) = &mut tasks[id.index];
            debug_assert_eq!(*gen, id.generation);

            task_option.as_mut().unwrap()
        };

        task.dependencies_left += offset;
        let dependencies_left = task.dependencies_left;

        debug_assert!(
            dependencies_left >= 0,
            "Dependencies left can never be less than 0"
        );

        if dependencies_left == 0 {
            let (gen, task2) = &mut tasks[id.index];
            debug_assert_eq!(*gen, id.generation);
            let task2 = task2.take().unwrap();
            self.work.enqueue(task2.task);
        }
    }

    /// # Locks
    /// Locks ``non_ready_tasks`` with write.
    fn resolve_dependency(&self, id: TaskId) {
        self.modify_dependency_count(id, -1);
    }

    /// # Locks
    /// Locks ``members`` write, and ``scopes`` write
    pub fn define_member(
        &self,
        errors: &mut ErrorCtx,
        loc: Location,
        scope_id: ScopeId,
        name: Ustr,
    ) -> Result<MemberId, ()> {
        let id = self.members.write().push(Member::new(name));

        self.bind_member_to_name(errors, scope_id, name, loc, id, true)?;
        Ok(id)
    }

    /// # Locks
    /// * ``scopes`` write
    /// * ``members`` write
    /// * ``non_ready_tasks`` write
    fn bind_member_to_name(
        &self,
        errors: &mut ErrorCtx,
        scope_id: ScopeId,
        name: Ustr,
        loc: Location,
        member_id: MemberId,
        is_public: bool,
    ) -> Result<(), ()> {
        let mut scopes = self.scopes.write();

        if scopes[scope_id].public_members.contains_key(&name)
            | scopes[scope_id].private_members.contains_key(&name)
        {
            errors.error(loc, format!("'{}' is already defined", name));
            return Err(());
        }

        if is_public {
            scopes[scope_id].public_members.insert(name, member_id);
        } else {
            scopes[scope_id].private_members.insert(name, member_id);
        };

        // FIXME: Performance problems here!! I don't really know how to fix this without messing
        // up the locks again.
        let wildcard_exports = scopes[scope_id].wildcard_exports.get_mut().clone();
        drop(scopes);

        if is_public {
            for dependant in wildcard_exports {
                self.bind_member_to_name(errors, dependant, name, loc, member_id, false)?;
            }
        }

        let scopes = self.scopes.read();
        let mut wanted_names = scopes[scope_id].wanted_names.write();
        if let Some(dependants) = wanted_names.remove(&name) {
            drop(wanted_names);
            drop(scopes);

            for &(kind, loc, dependant) in &dependants {
                let mut members = self.members.write();
                let member = &mut members[member_id];

                self.logger.log(format_args!(
                    "Dependant at '{:?}' found definition of '{}', now searches for the {:?} of it",
                    loc, member.name, kind,
                ));

                if !member.add_dependant(loc, kind, dependant) {
                    drop(members);
                    self.resolve_dependency(dependant);
                }
            }
        }

        Ok(())
    }

    /// Locks
    /// * ``non_ready_tasks`` write
    fn insert_task_into_task_list(&self, task: Task, dependencies_left: i32) -> TaskId {
        let task = NonReadyTask {
            dependencies_left,
            task,
        };

        let mut non_ready_tasks = self.non_ready_tasks.lock();
        if let Some(index) = non_ready_tasks.iter().position(|(_gen, val)| val.is_none()) {
            let generation = non_ready_tasks[index].0 + 1;
            non_ready_tasks[index] = (generation, Some(task));
            TaskId { generation, index }
        } else {
            let index = non_ready_tasks.len();
            non_ready_tasks.push((0, Some(task)));
            TaskId {
                generation: 0,
                index,
            }
        }
    }

    /// # Locks
    /// * ``scopes`` read
    /// * ``members`` write
    /// * ``non_ready_tasks`` write
    /// * ``functions`` write
    pub fn queue_task(&self, deps: DependencyList, task: Task) {
        // We start at this instead of zero so that even if some dependencies are resolved while we
        // are adding them, the count doesn't ever reach zero again. This is important, so that the
        // task isn't deployed before it's ready.
        const DEPENDENCY_COUNT_OFFSET: i32 = i32::MAX / 2;
        let id = self.insert_task_into_task_list(task, DEPENDENCY_COUNT_OFFSET);

        let mut num_deps = 0;
        for (loc, dep_kind) in deps.deps {
            match dep_kind {
                DepKind::MemberByName(scope_id, dep_name, dep_kind) => {
                    let scopes = self.scopes.read();
                    let scope = &scopes[scope_id];
                    let mut scope_wanted_names = scope.wanted_names.write();

                    if let Some(dep_id) = scope.get(dep_name) {
                        drop(scope_wanted_names);
                        drop(scopes);

                        let members = self.members.write();
                        if members[dep_id].add_dependant(loc, dep_kind, id) {
                            num_deps += 1;
                        }
                    } else {
                        num_deps += 1;
                        self.logger.log(format_args!(
                            "Undefined identifier '{}' in scope {}, wants {:?} of it",
                            dep_name, scope_id.0, dep_kind
                        ));

                        let wanted = scope_wanted_names.entry(dep_name).or_insert_with(Vec::new);
                        wanted.push((dep_kind, loc, id));
                    }
                }
                DepKind::Callable(function_id) => {
                    //
                    // Recursively depend on 'callable' functions, essentially we have to add more functions
                    // that haven't been added yet.
                    //
                    let functions = self.functions.read();
                    let loc = Location::start(
                        "Temporary location placeholder because I'm lazy bum".into(),
                    );
                    insert_callable_dependency_recursive(
                        &*functions,
                        function_id,
                        loc,
                        id,
                        &mut num_deps,
                    );
                    drop(functions);
                }
            }
        }

        let mut non_ready_tasks = self.non_ready_tasks.lock();
        let num_dependencies = &mut non_ready_tasks[id.index]
            .1
            .as_mut()
            .unwrap()
            .dependencies_left;

        *num_dependencies -= DEPENDENCY_COUNT_OFFSET;
        *num_dependencies += num_deps;

        if *num_dependencies == 0 {
            // If we are already done, well, we can just take the thing.
            let task = non_ready_tasks[id.index].1.take().unwrap();
            self.work.enqueue(task.task);
        }
    }
}

fn insert_callable_dependency_recursive(
    functions: &IdVec<FunctionId, Function>,
    function_id: FunctionId,
    loc: Location,
    task_id: TaskId,
    num_deps: &mut i32,
) {
    if functions[function_id].insert_dependant(task_id) {
        // It is not already defined and we do not depend on it already.

        match &functions[function_id].routine {
            DependableOption::Some((calling, _routine)) => {
                // It is defined, but not sure it's callable currently, so we have to recurse.
                for &it in calling.iter() {
                    insert_callable_dependency_recursive(functions, it, loc, task_id, num_deps);
                }
            }
            DependableOption::None(dependants) => {
                *num_deps += 1;
                dependants.lock().push((loc, task_id));
            }
        }
    }
}

#[derive(Default)]
struct Scope {
    // FIXME: Have these store the location where the thing was bound to a name as well.
    // At least in the public_members, since those are usually not imported but bound in the scope?
    // However, even private_members would have a use for the location of the import/library
    public_members: UstrMap<MemberId>,
    private_members: UstrMap<MemberId>,
    wanted_names: RwLock<UstrMap<Vec<(MemberDep, Location, TaskId)>>>,
    wildcard_exports: RwLock<Vec<ScopeId>>,
}

impl Scope {
    fn get(&self, name: Ustr) -> Option<MemberId> {
        let public = self.public_members.get(&name).copied();
        public.or_else(|| self.private_members.get(&name).copied())
    }
}

struct Function {
    // FIXME: We should use this location later to generate diagnostics. Though can you even have
    // recursion errors?
    #[allow(unused)]
    loc: Location,

    /// This is a little strange; depending on this does not mean depending on the definition of
    /// the routine, it means to depend on the routine being callable. What this means in practice,
    /// is that once this is defined, it will add all of the things this function calls to your
    /// dependency list as well(unless they are already called). Once a function has been
    /// determined to be callable, it will set its dependants to None so that we can avoid useless
    /// overhead.
    routine: DependableOption<(Vec<FunctionId>, Arc<Routine>)>,

    /// This is a list of all the tasks that are depending on this to be callable, to avoid
    /// infinite recursion when figuring out the dependency tree of this.
    /// Once it's determined that this function can be called safely, this can be set to none.
    dependants: Option<Mutex<HashSet<TaskId>>>,
}

impl Function {
    /// Tries to insert a dependant. Returns true if it could insert it, returns false if either
    /// dependants is None or the given id is already in the list of dependants.
    fn insert_dependant(&self, id: TaskId) -> bool {
        match &self.dependants {
            Some(dependants) => dependants.lock().insert(id),
            None => false,
        }
    }
}

struct Member {
    name: Ustr,
    type_: DependableOption<(Type, Arc<MemberMetaData>)>,
    value: DependableOption<ConstantRef>,

    /// So this is pretty confusing, and needs some writing up to both help me now and in the
    /// future.
    ///
    /// 'callable' means we can definitely call any function inside of a member. However,
    /// not all function calls need this to work, in fact, most shouldn't. If you just have a
    /// normal function call, it will instead look at the value of a member, see that it's a
    /// function, and then depend on that function being callable. The reason this still exists is
    /// for edge cases; what if you have an anonymous constant calling a function? What if you have
    /// a struct with function pointers inside? In those cases, this is only set once all the
    /// functions inside are callable. You could see it as if this is very conservative, and very
    /// secure, while the normal way to do it is less conservative, which means more complexity,
    /// but it's also more versatile, allowing for things like recursion.
    ///
    /// The point is this; for a Member which is just a function, this flag doesn't matter much,
    /// except if it's used in type expressions or constant expressions. The functions callability
    /// will be checked through the function part of the dependency system. However, this flag is
    /// always used for more complex types, but that on the other hand does not allow for
    /// recursion.
    callable: DependableOption<()>,
}

impl Member {
    fn add_dependant(&self, loc: Location, dep: MemberDep, dependant: TaskId) -> bool {
        match dep {
            MemberDep::Type => self.type_.add_dependant(loc, dependant),
            MemberDep::Value => self.value.add_dependant(loc, dependant),
            MemberDep::ValueAndCallableIfFunction => self.callable.add_dependant(loc, dependant),
        }
    }
}

#[derive(Debug, Clone)]
pub enum MemberMetaData {
    None,
    Function {
        arg_names: Vec<Ustr>,
        default_values: Vec<ConstantRef>,
    },
}

impl Member {
    fn new(name: Ustr) -> Self {
        Self {
            name,
            type_: DependableOption::None(default()),
            value: DependableOption::None(default()),
            callable: DependableOption::None(default()),
        }
    }
}

pub enum DependableOption<T> {
    Some(T),
    None(Mutex<Vec<(Location, TaskId)>>),
}

impl<T> DependableOption<T> {
    fn add_dependant(&self, loc: Location, dependant: TaskId) -> bool {
        match self {
            Self::Some(_) => false,
            Self::None(dependants) => {
                dependants.lock().push((loc, dependant));
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BuiltinFunction {
    StdoutWrite,
    StdoutFlush,
    StdinGetLine,

    MemCopy,
    MemCopyNonOverlapping,

    Alloc,
    Dealloc,
}

struct NonReadyTask {
    dependencies_left: i32,
    task: Task,
}

pub enum Task {
    Parse(Option<(Location, ScopeId)>, PathBuf),
    TypeMember(MemberId, crate::locals::LocalVariables, crate::parser::Ast),
    EmitMember(MemberId, crate::locals::LocalVariables, crate::typer::Ast),
    EvaluateMember(MemberId, crate::ir::UserDefinedRoutine),
    FlagMemberCallable(MemberId),
    TypeFunction(
        FunctionId,
        crate::locals::LocalVariables,
        Arc<crate::parser::Ast>,
        Type,
        Type,
    ),
    EmitFunction(
        FunctionId,
        crate::locals::LocalVariables,
        crate::typer::Ast,
        Type,
    ),
}

impl fmt::Debug for Task {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Task::Parse(_, buf) => write!(f, "parse({:?})", buf),
            Task::TypeMember(id, _, _) => write!(f, "type_member({:?})", id),
            Task::EmitMember(id, _, _) => write!(f, "emit_member({:?})", id),
            Task::EvaluateMember(id, _) => write!(f, "evaluate_member({:?})", id),
            Task::FlagMemberCallable(id) => write!(f, "flag_member_callable({:?}", id),
            Task::TypeFunction(id, _, _, _, _) => write!(f, "type_function({:?})", id),
            Task::EmitFunction(id, _, _, _) => write!(f, "emit_function({:?})", id),
        }
    }
}

fn default<T: Default>() -> T {
    T::default()
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct FunctionId(usize);

impl Id for FunctionId {}

impl From<usize> for FunctionId {
    fn from(other: usize) -> Self {
        Self(other)
    }
}

impl Into<usize> for FunctionId {
    fn into(self) -> usize {
        self.0
    }
}

impl fmt::Debug for FunctionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct MemberId(usize);

impl Id for MemberId {}

impl From<usize> for MemberId {
    fn from(other: usize) -> Self {
        Self(other)
    }
}

impl Into<usize> for MemberId {
    fn into(self) -> usize {
        self.0
    }
}

impl fmt::Debug for MemberId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ScopeId(usize);

impl Id for ScopeId {}

impl From<usize> for ScopeId {
    fn from(other: usize) -> Self {
        Self(other)
    }
}

impl Into<usize> for ScopeId {
    fn into(self) -> usize {
        self.0
    }
}

impl fmt::Debug for ScopeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TaskId {
    generation: u32,
    index: usize,
}

impl fmt::Debug for TaskId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(gen: {}, {})", self.generation, self.index)
    }
}
