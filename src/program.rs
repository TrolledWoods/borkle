use crate::command_line_arguments::Arguments;
use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::id::{Id, IdVec};
use crate::ir::Routine;
use crate::location::Location;
use crate::logging::Logger;
use crate::parser::Ast;
use crate::thread_pool::{ThreadContext, WorkPile};
use crate::type_infer::AstVariantId;
use crate::types::{PointerInType, Type, TypeKind};
use constant::{Constant, ConstantRef};
use parking_lot::{Mutex, RwLock, MutexGuard};
use std::alloc;
use std::collections::HashSet;
use std::fmt;
use std::path::{Path, PathBuf};
use std::ptr::NonNull;
use std::sync::Arc;
use ustr::{Ustr, UstrMap, UstrSet};
use std::sync::atomic::AtomicU64;
use syncvec::SyncVec;

pub mod constant;

// This is a hack aruond non-self referential types, by dividing this we know this lives
// longer than the program, and thus the program can hold references into this.
#[derive(Default)]
pub struct PreProgram {
    scopes: SyncVec<Scope>,
    members: SyncVec<Member>,
}

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

    pub lib_lines_of_code: AtomicU64,
    pub user_lines_of_code: AtomicU64,

    pre_program: &'static PreProgram,

    poly_members: RwLock<IdVec<PolyMemberId, PolyMember>>,

    external_symbols: Mutex<UstrSet>,
    constant_data: Mutex<Vec<Constant>>,

    functions: RwLock<IdVec<FunctionId, Function>>,
    non_ready_tasks: Mutex<Vec<(u32, Option<NonReadyTask>)>>,
    builtins: [RwLock<BuiltinDefinition>; Builtin::Count as usize],

    work: WorkPile,

    // FIXME: This shouldn't be public, but is for now so that the thread pool can do things with
    // it.
    pub loaded_files: Mutex<UstrMap<ScopeId>>,
    file_contents: Mutex<UstrMap<Arc<String>>>,
}

impl Program {
    /// Creates a new program. Leaks memory!! That's because this is only designed to
    /// run once in a single compiler run, otherwise the whole codebase needs to be infested
    /// with incredibly annoying lifetimes, which is possible, and may be something that I'd
    /// want to do in the future, but not now.
    pub fn new(logger: Logger, arguments: Arguments) -> Self {
        let pre_program = Box::leak(Box::new(PreProgram::default()));
        Self {
            pre_program,
            arguments,
            logger,
            builtins: [(); Builtin::Count as usize].map(|_| RwLock::new(BuiltinDefinition::Undefined(Vec::new()))),
            lib_lines_of_code: AtomicU64::new(0),
            user_lines_of_code: AtomicU64::new(0),
            poly_members: default(),
            external_symbols: default(),
            non_ready_tasks: default(),
            file_contents: default(),
            functions: default(),
            constant_data: default(),
            work: WorkPile::new(),
            loaded_files: default(),
        }
    }

    pub fn file_contents(&mut self) -> &mut UstrMap<Arc<String>> {
        self.file_contents.get_mut()
    }

    pub fn add_external_symbol(&self, symbol_name: Ustr) {
        self.external_symbols.lock().insert(symbol_name);
    }

    pub fn external_symbols(&self) -> MutexGuard<'_, UstrSet> {
        self.external_symbols.lock()
    }

    pub fn constant_data(&self) -> MutexGuard<'_, Vec<Constant>> {
        self.constant_data.lock()
    }

    pub fn work(&self) -> &WorkPile {
        &self.work
    }

    pub fn check_for_completion(&mut self, errors: &mut ErrorCtx) {
        for scope in self.pre_program.scopes.iter() {
            let wanted_names = scope.wanted_names.read();
            for (&name, dependants) in wanted_names.iter() {
                for &(_, loc, _) in dependants {
                    errors.info(loc, "Dependant here".to_string());
                }
                errors.global_error(format!("'{}' is not defined", name));
            }

            let public_members = scope.public_members.read();
            for (&name, &id) in public_members.iter() {
                if let PolyOrMember::Member(member) = id {
                    if member.0.type_.read().to_option().is_none() {
                        errors.global_error(format!("'{}' cannot be computed", name));
                    } else if member.0.kind == MemberKind::Const && member.0.value.read().to_option().is_none() {
                        errors.global_error(format!("'{}' cannot be computed(value)", name));
                    }
                }
            }
        }
    }

    pub fn get_polymember_loc(&self, id: PolyMemberId) -> Location {
        self.poly_members.read()[id].loc
    }

    pub fn get_function_loc(&self, id: FunctionId) -> Location {
        self.functions.read()[id].loc
    }

    /// Locks
    /// * ``functions`` write
    pub fn insert_defined_function(
        &self,
        loc: Location,
        calls: Vec<FunctionId>,
        routine: Routine,
    ) -> FunctionId {
        profile::profile!("Insert defined function");
        let mut functions = self.functions.write();
        functions.push(Function {
            loc,
            routine: DependableOption::Some((calls, Arc::new(routine))),
            dependants: Mutex::new(Some(default())),
        })
    }

    pub fn flag_function_callable(&self, function: FunctionId) {
        let functions = self.functions.read();
        set_callable_recursive(&*functions, function);
    }

    /// Locks
    /// * ``functions`` write
    pub fn insert_function(&self, loc: Location) -> FunctionId {
        profile::profile!("Insert function");
        let mut functions = self.functions.write();
        functions.push(Function {
            loc,
            routine: DependableOption::None(default()),
            dependants: Mutex::new(Some(default())),
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
    ) -> bool {
        profile::profile!("Set routine of function");
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

            true
        } else {
            self.logger.log(format_args!("Redundant routine emission!"));
            false
        }
    }

    pub fn get_routines<'a>(&'a self) -> RoutinesHandle<'a> {
        let functions = self.functions.read();

        RoutinesHandle {
            functions,
        }
    }

    /// Locks
    /// * ``functions`` read
    pub fn get_routine(&self, id: FunctionId) -> Option<Arc<Routine>> {
        profile::profile!("Get routine");
        let functions = self.functions.read();

        // FIXME: This is not very good for performance, we want to avoid cloning arcs. Could we
        // have an unsafe version of get_routine that makes assumptions?
        functions[id]
            .routine
            .to_option()
            .map(|(_, x)| Arc::clone(x))
    }

    /// # Locks
    /// * ``scopes`` write
    pub fn create_scope(&self) -> ScopeId {
        profile::profile!("Create scope");
        let (_, ptr) = self.pre_program.scopes.push(default());
        ScopeId(ptr)
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
        profile::profile!("Insert wildcard export");
        let mut wildcards = from.0.wildcard_exports.write();

        if wildcards.contains(&to) {
            errors.error(loc, "This is imported twice".to_string());
            return Err(());
        }

        wildcards.push(to);
        // FIXME: I don't really know how to fix this performance wise without messing up the
        // locks.
        let public_members = from.0.public_members.read().clone();
        drop(wildcards);

        for (name, member_id) in public_members {
            self.bind_member_to_name(errors, to, name, loc, member_id, false)?;
        }

        Ok(())
    }

    pub fn get_member_id_from_builtin(&self, builtin_kind: Builtin) -> Option<PolyOrMember> {
        profile::profile!("get_member_id_from_builtin");
        let builtin = self.builtins[builtin_kind as usize].read();
        if let BuiltinDefinition::Defined(member_id) = *builtin {
            Some(member_id)
        } else {
            None
        }
    }

    /// Locks
    /// * ``scopes`` read
    pub fn get_member_id(&self, scope: ScopeId, name: Ustr) -> Option<PolyOrMember> {
        profile::profile!("Get member id");
        let public = scope.0.public_members.read().get(&name).copied();
        public.or_else(|| scope.0.private_members.read().get(&name).copied())
    }

    pub fn poly_member_name(&self, id: PolyMemberId) -> Ustr {
        profile::profile!("Poly member name");
        let members = self.poly_members.read();
        members[id].name
    }

    /// Locks
    /// * ``members`` read
    pub fn poly_or_member_name(&self, id: PolyOrMember) -> Ustr {
        match id {
            PolyOrMember::Poly(id) => self.poly_member_name(id),
            PolyOrMember::Member(id) => id.name(),
        }
    }

    /// Locks
    /// * ``members`` read
    pub fn get_value_of_member(&self, id: MemberId) -> ConstantRef {
        profile::profile!("Get value of member");

        let v = *id.0.value.read().unwrap();
        v
    }

    pub fn get_polymember_yielddata(&self, id: PolyMemberId) -> (Arc<crate::typer::YieldData>, Arc<Vec<Option<(Ustr, Location)>>>) {
        profile::profile!("Get polymember yielddata");
        let poly_members = self.poly_members.read();
        let poly_member = &poly_members[id];
        (
            poly_member.yield_data.as_ref().unwrap().clone(),
            poly_member.args.clone()
        )
    }

    pub fn get_member_meta_data_and_kind(&self, id: PolyOrMember) -> (Arc<MemberMetaData>, MemberKind) {
        profile::profile!("program::get_member_meta_data_and_kind");
        match id {
            PolyOrMember::Member(id) => {
                let v = id.0.type_.read().unwrap().1.clone();
                (v, id.0.kind)
            }
            PolyOrMember::Poly(id) => {
                let members = self.poly_members.read();
                let v = members[id].type_.unwrap().clone();
                (v, members[id].kind)
            }
        }
    }

    pub fn get_member_meta_data(&self, id: PolyOrMember) -> Arc<MemberMetaData> {
        profile::profile!("program::get_member_meta_data");
        match id {
            PolyOrMember::Member(id) => {
                let v = id.0.type_.read().unwrap().1.clone();
                v
            }
            PolyOrMember::Poly(id) => {
                let members = self.poly_members.read();
                let v = members[id].type_.unwrap().clone();
                v
            }
        }
    }

    /// Locks
    /// * ``constant_data`` write
    fn insert_sub_buffers(&self, type_: &Type, data: *mut u8) {
        type_.get_pointers(|offset, ptr| {
            match ptr {
                PointerInType::Pointer(internal) => unsafe {
                    let ptr = *data.add(offset).cast::<*const u8>();
                    if !ptr.is_null() {
                        let sub_buffer = self.insert_buffer(internal, ptr);
                        *data.cast::<*const u8>() = sub_buffer.as_ptr();
                    }
                },
                PointerInType::Buffer(internal) => {
                    let buffer = unsafe { &mut *data.cast::<crate::types::BufferRepr>() };

                    if buffer.length != 0 {
                        // @Speed: This is not fast.
                        let usize_type = Type::new_int(crate::types::IntTypeKind::Usize);
                        let length_constant_ptr = self.insert_buffer(&usize_type, &buffer.length as *const usize as *const u8);
                        let length_constant_value = Type::new(TypeKind::ConstantValue(length_constant_ptr));
                        let length_constant = Type::new_with_args(TypeKind::Constant, Box::new([usize_type, length_constant_value]));
                        let array_type = Type::new_with_args(TypeKind::Array, Box::new([internal.clone(), length_constant]));
                        let sub_buffer = self.insert_buffer(&array_type, buffer.ptr);

                        buffer.ptr = sub_buffer.as_ptr() as *mut _;
                    } else {
                        buffer.ptr = std::ptr::null_mut();
                    }
                }
                PointerInType::Function { .. } => {}
            }
        });
    }

    pub fn add_file(&self, path: impl AsRef<Path>, is_library: bool) {
        profile::profile!("program::add_file");
        self.work
            .enqueue(Task::Parse {
                imported_at: None,
                is_library,
                path: path.as_ref().to_path_buf(),
            });
    }

    /// Locks
    /// * ``files`` write
    pub fn insert_file_contents(&self, name: Ustr, path: String) {
        profile::profile!("program::insert_file_contents");
        self.file_contents.lock().insert(name, Arc::new(path));
    }

    pub fn add_file_from_import(
        &self,
        path: impl AsRef<Path>,
        location: Location,
        from_scope: ScopeId,
        is_library: bool,
    ) {
        self.work.enqueue(Task::Parse {
            imported_at: Some((location, from_scope)),
            is_library,
            path: path.as_ref().to_path_buf(),
        });
    }

    /// Locks
    /// * ``constant_data`` write
    pub fn insert_raw_buffer_from_operation(
        &self,
        size: usize,
        align: usize,
        get_data: impl FnOnce(*mut u8),
    ) -> ConstantRef {
        profile::profile!("program::insert_raw_buffer_from_operation");
        if size == 0 {
            return ConstantRef::dangling();
        }

        let layout = alloc::Layout::from_size_align(size, align).unwrap();

        let owned_data = unsafe { alloc::alloc(layout) };
        get_data(owned_data);

        let mut constant_data = self.constant_data.lock();
        let slice_version = unsafe { std::slice::from_raw_parts(owned_data, size) };
        for pre_computed_constant in constant_data.iter() {
            if pre_computed_constant.type_.is_none()
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
            type_: None,
            size,
            align,
        };

        let const_ref = constant.as_ref();
        constant_data.push(constant);

        const_ref
    }

    /// # Locks
    /// * ``constant_data`` write
    pub fn insert_raw_buffer(&self, size: usize, align: usize, data: *const u8) -> ConstantRef {
        self.insert_raw_buffer_from_operation(size, align, |buf| unsafe {
            std::ptr::copy(data, buf, size)
        })
    }

    /// Locks
    /// * ``constant_data`` write
    pub fn insert_buffer_from_operation(
        &self,
        type_: &Type,
        get_data: impl FnOnce(*mut u8),
    ) -> ConstantRef {
        profile::profile!("program::insert_buffer_from_operation");
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
            if pre_computed_constant.type_.as_ref() == Some(type_)
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
            type_: Some(type_.clone()),
            size: type_.size(),
            align: type_.align(),
        };

        let const_ref = constant.as_ref();
        constant_data.push(constant);

        const_ref
    }

    /// # Locks
    /// * ``constant_data`` write
    pub fn insert_buffer(&self, type_: &Type, data: *const u8) -> ConstantRef {
        self.insert_buffer_from_operation(type_, |buf| unsafe {
            std::ptr::copy(data, buf, type_.size())
        })
    }

    pub fn flag_poly_member_type(&self, id: PolyMemberId, meta_data: MemberMetaData) {
        profile::profile!("program::flag_poly_member_type");
        let mut poly_members = self.poly_members.write();
        let old =
            std::mem::replace(&mut poly_members[id].type_, DependableOption::Some(Arc::new(meta_data)));
        drop(poly_members);

        if let DependableOption::None(dependencies) = old {
            for (_, dependency) in dependencies.into_inner() {
                self.resolve_dependency(dependency);
            }
        }
    }

    pub fn flag_poly_member_value(&self, id: PolyMemberId) {
        profile::profile!("program::flag_poly_member_value");
        let mut poly_members = self.poly_members.write();
        let old =
            std::mem::replace(&mut poly_members[id].value, DependableOption::Some(()));
        drop(poly_members);

        if let DependableOption::None(dependencies) = old {
            for (_, dependency) in dependencies.into_inner() {
                self.resolve_dependency(dependency);
            }
        }
    }

    pub fn flag_poly_member_value_and_callable_if_function(&self, id: PolyMemberId) {
        let mut poly_members = self.poly_members.write();
        let old =
            std::mem::replace(&mut poly_members[id].callable, DependableOption::Some(()));
        drop(poly_members);

        if let DependableOption::None(dependencies) = old {
            for (_, dependency) in dependencies.into_inner() {
                self.resolve_dependency(dependency);
            }
        }
    }

    pub fn flag_member_callable(&self, id: MemberId) {
        profile::profile!("program::flag_member_callable");
        let is_monomorphised = id.0.is_monomorphised;
        let old = std::mem::replace(&mut *id.0.callable.write(), DependableOption::Some(()));

        if let DependableOption::None(dependencies) = old {
            for (_, dependency) in dependencies.into_inner() {
                self.resolve_dependency(dependency);
            }
        } else if is_monomorphised {
            self.logger.log(format_args!(
                "{:?} was flagged callable twice! Oh no, inefficiency!",
                id
            ));
        } else {
            unreachable!("This shouldn't happen, ever");
        }
    }

    /// # Locks
    /// * ``constant_data`` write
    /// * ``members`` write
    /// * ``functions`` write
    pub fn set_value_of_member(&self, id: MemberId, value: ConstantRef) {
        profile::profile!("program::set_value_of_member");
        let is_monomorphised = id.0.is_monomorphised;
        let old = std::mem::replace(&mut *id.0.value.write(), DependableOption::Some(value));

        if let DependableOption::None(dependencies) = old {
            for (_, dependency) in dependencies.into_inner() {
                self.resolve_dependency(dependency);
            }
        } else if is_monomorphised {
            self.logger.log(format_args!(
                "{:?}(monomorphic variant) was evaluated twice! Oh no, inefficiency!",
                id
            ));
        } else {
            unreachable!("You can only set the value of a member once!");
        }
    }

    pub fn set_yield_data_of_poly_member(&self, id: PolyMemberId, yield_data: crate::typer::YieldData) {
        profile::profile!("program::set_yield_data_of_poly_member");
        let yield_data = Arc::new(yield_data);
        let mut poly_members = self.poly_members.write();
        let old = std::mem::replace(
            &mut poly_members[id].yield_data,
            Some(yield_data),
        );
        drop(poly_members);
        debug_assert!(old.is_none());
    }

    /// # Locks
    /// * ``members`` write
    pub fn set_type_of_member(&self, id: MemberId, type_: Type, meta_data: MemberMetaData) {
        profile::profile!("program::set_type_of_member");
        let is_monomorphised = id.0.is_monomorphised;
        let mut member_type = id.0.type_.write();
        let old = std::mem::replace(
            &mut *member_type,
            DependableOption::Some((type_, Arc::new(meta_data))),
        );
        drop(member_type);

        if let DependableOption::None(dependencies) = old {
            for (_, dependency) in dependencies.into_inner() {
                self.resolve_dependency(dependency);
            }
        } else if is_monomorphised {
            self.logger.log(format_args!(
                "{:?}(monomorphic variant) was typed twice! Oh no, inefficiency!",
                id
            ));
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
    #[track_caller]
    fn resolve_dependency(&self, id: TaskId) {
        self.modify_dependency_count(id, -1);
    }

    pub fn define_polymorphic_member(
        &self,
        errors: &mut ErrorCtx,
        loc: Location,
        scope_id: ScopeId,
        name: Ustr,
        args: Vec<Option<(Ustr, Location)>>,
        kind: MemberKind,
    ) -> Result<PolyMemberId, ()> {
        profile::profile!("program::define_polymorphic_member");
        let id = self
            .poly_members
            .write()
            .push(PolyMember::new(loc, name, args, kind));

        self.bind_member_to_name(errors, scope_id, name, loc, PolyOrMember::Poly(id), true)?;
        Ok(id)
    }

    pub fn get_num_poly_args(&self, id: PolyMemberId) -> usize {
        self.poly_members.read()[id].args.len()
    }

    pub fn monomorphise_poly_member<'a>(
        &'a self,
        errors: &mut ErrorCtx,
        thread_context: &mut ThreadContext<'a>,
        id: PolyMemberId,
        poly_args: &[Type],
        wanted_dep: MemberDep,
    ) -> Result<MemberId, ()> {
        profile::profile!("program::monomorphise_poly_member");

        // FIXME: Some redundant work going on, but because we do not have a centralized location
        // for things like ast:s in work, we can't do that. Could we have some kind of handle to a
        // task associated with a member, since that might let us get the data associated with that
        // task? Then we could like look if the member has a task currently running and just run
        // that for it here, so that we can do the processing immediately. Though that might not
        // work since that task qould already be enqueued since all the dependencies of it would
        // have been resolved already(if they weren't that'd be a bug).

        let mut poly_members = self.poly_members.write();

        debug_assert_eq!(
            poly_members[id].args.len(),
            poly_args.len(),
            "There has to be the same number of polymorphic arguments passed as ones that exist."
        );

        let cached = &poly_members[id].cached;
        let mut member_id = None;
        for (key, cached_member) in cached {
            if &**key == poly_args {
                member_id = Some(*cached_member);
            }
        }

        let member_kind = poly_members[id].kind;

        // Create a member to host the monomorphised thing, or grab one from the cached
        let member_id = member_id.unwrap_or_else(|| {
            let poly_member = &poly_members[id];
            let (_, ptr) = self.pre_program.members.push(Member::new(poly_member.loc, poly_member.name, true, member_kind));
            let member_id = MemberId(ptr);
            poly_members[id]
                .cached
                .push((poly_args.to_vec(), member_id));
            member_id
        });

        let yield_data = poly_members[id].yield_data.as_ref().unwrap().clone();
        let name = poly_members[id].name;
        drop(poly_members);

        // Is the thing we want already computed?
        match wanted_dep {
            MemberDep::Type if member_id.is_typed() => return Ok(member_id),
            MemberDep::Value if member_id.is_evaluated() => return Ok(member_id),
            MemberDep::ValueAndCallableIfFunction if member_id.is_callable() => {
                return Ok(member_id)
            }
            _ => {}
        }

        let mut yield_data = (*yield_data).clone();
        yield_data.insert_poly_params(self, poly_args);
        crate::typer::solve(errors, thread_context, self, &mut yield_data);
        let (dependency_list, mut locals, mut types, typed_ast, root_value_id, additional_info) = match crate::typer::finish(errors, yield_data)? {
            Ok(v) => v,
            Err(_) => todo!("Not done!"),
        };

        // FIXME: Calculate the member meta data here.
        self.set_type_of_member(member_id, types.value_to_compiler_type(root_value_id), MemberMetaData::None);

        if matches!(member_kind, MemberKind::Type { .. }) {
            debug_assert!(wanted_dep <= MemberDep::Type);

            return Ok(member_id);
        }

        if wanted_dep < MemberDep::Value {
            self.queue_task(
                dependency_list,
                Task::EmitMember(
                    member_id,
                    locals,
                    types,
                    additional_info,
                    typed_ast,
                )
            );

            // It's fine, it's already enough
            return Ok(member_id);
        }

        assert_ne!(wanted_dep, MemberDep::Value, "Depending on just the value shouldn't really happen in this place, because either you go full on callable or you depend on the type. If you need to depend on the value it monomorphises it by depending on the type and then calculates the type on the value individually.");

        // @HACK: Here we assume that stack frame id number 0 is the parent one.
        let (_, routine) = crate::emit::emit(thread_context, self, &mut locals, &mut types, &typed_ast, &additional_info, typed_ast.root_id(), AstVariantId::root(), true, name);
        let mut stack = crate::interp::Stack::new(2048);

        let mut call_stack = Vec::new();
        let Ok(result) = crate::interp::interp(self, &mut stack, &routine, &mut call_stack) else {
            println!("TEMP: No call stack error for monomorphise_poly_member yet, we should deduplicate these.");
            return Err(());
        };

        self.logger
            .log(format_args!("value '{}'", member_id.name()));

        let type_ = member_id.type_();
        let value = self.insert_buffer(&type_, result.as_ptr());

        self.set_value_of_member(member_id, value);
        self.flag_member_callable(member_id);
        
        /* TODO: Think about if this is necessary.
        */
        unsafe {
            type_.get_function_ids(value.as_ptr(), |function_id| {
                self.flag_function_callable(function_id);
            });
        }

        Ok(member_id)
    }

    /// # Locks
    /// Locks ``members`` write, and ``scopes`` write
    pub fn define_member(
        &self,
        errors: &mut ErrorCtx,
        loc: Location,
        scope_id: Option<ScopeId>,
        name: Ustr,
        kind: MemberKind,
    ) -> Result<MemberId, ()> {
        let (_, ptr) = self.pre_program.members.push(Member::new(loc, name, false, kind));
        let id = MemberId(ptr);

        if let Some(scope_id) = scope_id {
            self.bind_member_to_name(errors, scope_id, name, loc, PolyOrMember::Member(id), true)?;
        }
        Ok(id)
    }

    pub fn bind_member_to_builtin(
        &self,
        errors: &mut ErrorCtx,
        builtin: Builtin,
        loc: Location,
        member_id: PolyOrMember,
    ) -> Result<(), ()> {
        let mut builtin_def = self.builtins[builtin as usize].write();
        let old = std::mem::replace(&mut *builtin_def, BuiltinDefinition::Defined(member_id));
        drop(builtin_def);

        match old {
            BuiltinDefinition::Defined(_old_member_id) => {
                errors.error(loc, format!("`{:?}` is already defined", builtin));
                Err(())
            }
            BuiltinDefinition::Undefined(dependants) => {
                // @Copypasta: From bind_member_to_name
                match member_id {
                    PolyOrMember::Member(member_id) => {
                        for &(kind, loc, dependant) in &dependants {
                            self.logger.log(format_args!(
                                "Dependant at '{}' found definition of '{}', now searches for the {:?} of it",
                                loc, member_id.0.name, kind,
                            ));

                            if !member_id.0.add_dependant(loc, kind, dependant) {
                                self.resolve_dependency(dependant);
                            }
                        }
                    }
                    PolyOrMember::Poly(poly_id) => {
                        for &(kind, loc, dependant) in &dependants {
                            let mut members = self.poly_members.write();
                            let member = &mut members[poly_id];

                            self.logger.log(format_args!(
                                "Dependant at '{}' found definition of '{}', now searches for the {:?} of it",
                                loc, member.name, kind,
                            ));

                            if !member.add_dependant(loc, kind, dependant) {
                                drop(members);
                                self.resolve_dependency(dependant);
                            }
                        }
                    }
                }

                Ok(())
            }
        }
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
        member_id: PolyOrMember,
        is_public: bool,
    ) -> Result<(), ()> {
        let contains_public_name = scope_id.0.public_members.read().contains_key(&name);
        let contains_private_name = scope_id.0.private_members.read().contains_key(&name);
        if contains_public_name || contains_private_name {
            errors.error(loc, format!("'{}' is already defined", name));
            return Err(());
        }

        if is_public {
            scope_id.0.public_members.write().insert(name, member_id);
        } else {
            scope_id.0.private_members.write().insert(name, member_id);
        };

        // FIXME: Performance problems here!! I don't really know how to fix this without messing
        // up the locks again.
        let wildcard_exports = scope_id.0.wildcard_exports.write().clone();

        if is_public {
            for dependant in wildcard_exports {
                self.bind_member_to_name(errors, dependant, name, loc, member_id, false)?;
            }
        }

        let mut wanted_names = scope_id.0.wanted_names.write();
        if let Some(dependants) = wanted_names.remove(&name) {
            drop(wanted_names);

            match member_id {
                PolyOrMember::Member(member_id) => {
                    for &(kind, loc, dependant) in &dependants {
                        self.logger.log(format_args!(
                                "Dependant at '{}' found definition of '{}', now searches for the {:?} of it",
                                loc, member_id.0.name, kind,
                        ));

                        if !member_id.0.add_dependant(loc, kind, dependant) {
                            self.resolve_dependency(dependant);
                        }
                    }
                }
                PolyOrMember::Poly(poly_id) => {
                    for &(kind, loc, dependant) in &dependants {
                        let mut members = self.poly_members.write();
                        let member = &mut members[poly_id];

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
        self.logger.log(format_args!(
            "queuing task {:?} with dependencies {:?}", task, deps,
        ));

        // We start at this instead of zero so that even if some dependencies are resolved while we
        // are adding them, the count doesn't ever reach zero again. This is important, so that the
        // task isn't deployed before it's ready.
        const DEPENDENCY_COUNT_OFFSET: i32 = i32::MAX / 2;
        let id = self.insert_task_into_task_list(task, DEPENDENCY_COUNT_OFFSET);

        let mut num_deps = 0;
        for (loc, dep_kind) in deps.deps {
            match dep_kind {
                DepKind::MemberByBuiltin(builtin, dep_kind) => {
                    let mut builtin_def = self.builtins[builtin as usize].write();

                    match *builtin_def {
                        BuiltinDefinition::Defined(dep_id) => {
                            drop(builtin);

                            match dep_id {
                                PolyOrMember::Poly(dep_id) => {
                                    let members = self.poly_members.read();
                                    if members[dep_id].add_dependant(loc, dep_kind, id) {
                                        num_deps += 1;
                                    }
                                }
                                PolyOrMember::Member(dep_id) => {
                                    if dep_id.0.add_dependant(loc, dep_kind, id) {
                                        num_deps += 1;
                                    }
                                }
                            }
                        }
                        BuiltinDefinition::Undefined(ref mut dependants) => {
                            num_deps += 1;
                            self.logger.log(format_args!(
                                "Undefined builtin '{:?}', wants {:?} of it",
                                builtin, dep_kind
                            ));

                            dependants.push((dep_kind, loc, id));
                        }
                    }
                    
                }
                DepKind::MemberByName(scope_id, dep_name, dep_kind) => {
                    let mut scope_wanted_names = scope_id.0.wanted_names.write();

                    if let Some(dep_id) = scope_id.0.get(dep_name) {
                        drop(scope_wanted_names);

                        match dep_id {
                            PolyOrMember::Poly(dep_id) => {
                                let members = self.poly_members.read();
                                if members[dep_id].add_dependant(loc, dep_kind, id) {
                                    num_deps += 1;
                                }
                            }
                            PolyOrMember::Member(dep_id) => {
                                if dep_id.0.add_dependant(loc, dep_kind, id) {
                                    num_deps += 1;
                                }
                            }
                        }
                    } else {
                        num_deps += 1;
                        self.logger.log(format_args!(
                            "Undefined identifier '{}' in scope {:?}, wants {:?} of it",
                            dep_name, scope_id, dep_kind
                        ));

                        let wanted = scope_wanted_names.entry(dep_name).or_insert_with(Vec::new);
                        wanted.push((dep_kind, loc, id));
                    }
                }
                DepKind::Member(dep_id, dep_kind) => {
                    if dep_id.0.add_dependant(loc, dep_kind, id) {
                        num_deps += 1;
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

fn set_callable_recursive(functions: &IdVec<FunctionId, Function>, function_id: FunctionId) {
    let mut dependants = functions[function_id].dependants.lock();
    let old = std::mem::replace(&mut *dependants, None);
    drop(dependants);

    // If it's None, someone has already set this to callable recursively so we don't have to
    // bother with doing it again.
    if old.is_some() {
        let (calling, _routine) = functions[function_id].routine.unwrap();

        for &it in calling.iter() {
            set_callable_recursive(functions, it);
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

enum BuiltinDefinition {
    Defined(PolyOrMember),
    Undefined(Vec<(MemberDep, Location, TaskId)>),
}

#[derive(Default)]
struct Scope {
    // FIXME: Have these store the location where the thing was bound to a name as well.
    // At least in the public_members, since those are usually not imported but bound in the scope?
    // However, even private_members would have a use for the location of the import/library
    public_members: RwLock<UstrMap<PolyOrMember>>,
    private_members: RwLock<UstrMap<PolyOrMember>>,
    wanted_names: RwLock<UstrMap<Vec<(MemberDep, Location, TaskId)>>>,
    wildcard_exports: RwLock<Vec<ScopeId>>,
}

impl Scope {
    fn get(&self, name: Ustr) -> Option<PolyOrMember> {
        let public = self.public_members.read().get(&name).copied();
        public.or_else(|| self.private_members.read().get(&name).copied())
    }
}

pub struct RoutinesHandle<'a> {
    functions: parking_lot::RwLockReadGuard<'a, IdVec<FunctionId, Function>>,
}

impl RoutinesHandle<'_> {
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = (FunctionId, &'a Arc<Routine>)> {
        self.functions.iter().enumerate().filter_map(|(i, v)| match v.routine {
            DependableOption::Some((_, ref v)) => Some((FunctionId(i), v)),
            DependableOption::None { .. } => None,
        })
    }
}

struct Function {
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
    dependants: Mutex<Option<HashSet<TaskId>>>,
}

impl Function {
    /// Tries to insert a dependant. Returns true if it could insert it, returns false if either
    /// dependants is None or the given id is already in the list of dependants.
    fn insert_dependant(&self, id: TaskId) -> bool {
        let mut dependants = self.dependants.lock();
        match &mut *dependants {
            Some(dependants) => dependants.insert(id),
            None => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemberKind {
    Type { is_aliased: bool },
    Const,
}

struct PolyMember {
    name: Ustr,

    kind: MemberKind,
    loc: Location,
    yield_data: Option<Arc<crate::typer::YieldData>>,
    args: Arc<Vec<Option<(Ustr, Location)>>>,

    // These do not contain the actual types(because monomorphisation has to happen), however, they
    // do express the ability to calculate these things. Basically, if you monomorphise this
    // polymember into a normal member, these represent what parts of that member you can then
    // calculate.
    type_: DependableOption<Arc<MemberMetaData>>,
    value: DependableOption<()>,
    callable: DependableOption<()>,

    // cached_variants:
    cached: Vec<(Vec<Type>, MemberId)>,
}

impl PolyMember {
    fn new(
        loc: Location,
        name: Ustr,
        args: Vec<Option<(Ustr, Location)>>,
        kind: MemberKind,
    ) -> Self {
        Self {
            kind,

            loc,
            name,
            args: Arc::new(args),
            yield_data: None,

            type_: DependableOption::None(default()),
            value: DependableOption::None(default()),
            callable: DependableOption::None(default()),

            cached: Vec::new(),
        }
    }

    fn add_dependant(&self, loc: Location, dep: MemberDep, dependant: TaskId) -> bool {
        match dep {
            MemberDep::Type => self.type_.add_dependant(loc, dependant),
            MemberDep::Value => self.value.add_dependant(loc, dependant),
            MemberDep::ValueAndCallableIfFunction => self.callable.add_dependant(loc, dependant),
        }
    }
}

struct Member {
    is_monomorphised: bool,

    kind: MemberKind,
    #[allow(unused)]
    loc: Location,
    name: Ustr,
    type_: RwLock<DependableOption<(Type, Arc<MemberMetaData>)>>,

    // None if the member is a type,
    // Some if it's a value.
    value: RwLock<DependableOption<ConstantRef>>,

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
    callable: RwLock<DependableOption<()>>,
}

impl Member {
    fn new(loc: Location, name: Ustr, is_monomorphised: bool, kind: MemberKind) -> Self {
        Self {
            is_monomorphised,
            kind,
            loc,
            name,
            type_: RwLock::new(DependableOption::None(default())),
            value: RwLock::new(DependableOption::None(default())),
            callable: RwLock::new(DependableOption::None(default())),
        }
    }

    fn add_dependant(&self, loc: Location, dep: MemberDep, dependant: TaskId) -> bool {
        match dep {
            MemberDep::Type => self.type_.read().add_dependant(loc, dependant),
            MemberDep::Value => self.value.read().add_dependant(loc, dependant),
            MemberDep::ValueAndCallableIfFunction => self.callable.read().add_dependant(loc, dependant),
        }
    }
}

#[derive(Debug, Clone)]
pub enum MemberMetaData {
    None,
    Function(FunctionMetaData),
}

#[derive(Default, Debug, Clone)]
pub struct FunctionMetaData {
    pub arguments: Vec<FunctionArgumentInfo>,
}

#[derive(Debug, Clone)]
pub struct FunctionArgumentInfo {
    // It's not always possible to extract a name if you have
    // pattern matches.
    pub name: Option<(Ustr, Location)>,
    pub var_args: Option<Location>,
}

pub enum DependableOption<T> {
    Some(T),
    None(Mutex<Vec<(Location, TaskId)>>),
}

impl<T> DependableOption<T> {
    fn is_some(&self) -> bool {
        match self {
            Self::Some(_) => true,
            Self::None(_) => false,
        }
    }

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
#[repr(usize)]
pub enum Builtin {
    CallingConvention,
    Target,
    CString,
    Count,
}

impl Builtin {
    pub fn builtin_type_from_string(name: &str) -> Option<Self> {
        match name {
            "CallingConvention" => Some(Self::CallingConvention),
            "Target" => Some(Self::Target),
            "CString" => Some(Self::CString),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BuiltinFunction {
    CreateExe,
    CreateBir,

    StdoutWrite,
    StdoutFlush,
    StdinRead,

    Assert,

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
    TypePolyMember {
        member_id: PolyMemberId, 
        ast: Ast,
        locals: crate::locals::LocalVariables,
        dependencies: DependencyList,
        poly_args: Vec<crate::parser::PolyArgumentInfo>,
        member_kind: MemberKind,
    },
    FlagPolyMember(PolyMemberId, MemberDep, DependencyList),

    Parse { 
        imported_at: Option<(Location, ScopeId)>,
        is_library: bool,
        path: PathBuf,
    },
    TypeMember {
        member_id: MemberId,
        ast: Ast,
        locals: crate::locals::LocalVariables,
        member_kind: MemberKind,
    },
    EmitMember(MemberId, crate::locals::LocalVariables, crate::type_infer::TypeSystem, crate::typer::AdditionalInfo, crate::typer::Ast),
    EvaluateMember(MemberId, crate::ir::UserDefinedRoutine),
    FlagMemberCallable(MemberId),
    EmitFunction(
        crate::locals::LocalVariables,
        crate::type_infer::TypeSystem,
        crate::typer::AdditionalInfo,
        crate::typer::Ast,
        crate::ast::NodeId,
        Type,
        FunctionId,
        AstVariantId,
        Ustr,
    ),
}

impl fmt::Debug for Task {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Task::FlagPolyMember(id, dep_kind, _) => {
                write!(f, "flag_member_callable({:?}, {:?})", id, dep_kind)
            }

            Task::Parse { path, .. } => write!(f, "parse({})", path.display()),
            Task::TypeMember { member_id, .. } => write!(f, "type_member({:?})", member_id),
            Task::TypePolyMember { member_id, .. } => write!(f, "type_poly_member({:?})", member_id),
            Task::EmitMember(id, ..) => write!(f, "emit_member({:?})", id),
            Task::EvaluateMember(id, _) => write!(f, "evaluate_member({:?})", id),
            Task::FlagMemberCallable(id) => write!(f, "flag_member_callable({:?})", id),
            Task::EmitFunction(_, _, _, _, _, _, id, _, _) => write!(f, "emit_function({:?})", id),
        }
    }
}

fn default<T: Default>() -> T {
    T::default()
}

pub fn constant_to_str(type_: &Type, value: ConstantRef, _rec: usize) -> String {
    match type_.kind() {
        TypeKind::Int => {
            let args = type_.args();
            let &TypeKind::IntSigned(signed) = args[0].kind() else { unreachable!() };
            let &TypeKind::IntSize(mut size) = args[1].kind() else { unreachable!() };

            // @Cleanup: There should be a function for this.
            if size == 0 { size = 8; }
            debug_assert!(size.is_power_of_two() && size <= 8);

            let size = size as usize;

            let mut big_int = [0; 16];
            unsafe {
                std::ptr::copy_nonoverlapping(value.as_ptr(), big_int.as_mut_ptr(), size);
            }

            if signed && (big_int[size] & 0x80) > 0 {
                big_int[size + 1..].fill(0xff);
            }

            format!("{}", i128::from_le_bytes(big_int))
        }
        TypeKind::Bool => {
            let byte = unsafe { *value.as_ptr() };
            match byte {
                0 => "false".to_string(),
                1 => "true".to_string(),
                num => format!("<invalid bool value {}>", num),
            }
        }
        TypeKind::Function { .. } => {
            let id = unsafe { *value.as_ptr().cast::<FunctionId>() };
            format!("func({})", id.0)
        }
        _ => {
            format!("(cannot format {})", type_)
        }
    }
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

impl From<FunctionId> for usize {
    fn from(other: FunctionId) -> usize {
        other.0
    }
}

impl fmt::Debug for FunctionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PolyOrMember {
    Poly(PolyMemberId),
    Member(MemberId),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct PolyMemberId(usize);

impl Id for PolyMemberId {}

impl From<usize> for PolyMemberId {
    fn from(other: usize) -> Self {
        Self(other)
    }
}

impl From<PolyMemberId> for usize {
    fn from(other: PolyMemberId) -> usize {
        other.0
    }
}

impl fmt::Debug for PolyMemberId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct MemberId(&'static Member);

impl MemberId {
    #[inline]
    pub fn name(self) -> Ustr {
        self.0.name
    }

    pub fn type_(self) -> Type {
        let v = self.0.type_.read().unwrap().0.clone();
        v
    }

    pub fn value(self) -> ConstantRef {
        let v = *self.0.value.read().to_option().unwrap();
        v
    }

    pub fn is_typed(self) -> bool {
        self.0.type_.read().is_some()
    }

    pub fn is_evaluated(self) -> bool {
        self.0.value.read().is_some()
    }

    pub fn is_callable(self) -> bool {
        self.0.callable.read().is_some()
    }
}

impl std::cmp::PartialEq for MemberId {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl std::cmp::Eq for MemberId {}


impl fmt::Debug for MemberId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:p}", self.0)
    }
}

#[derive(Clone, Copy)]
pub struct ScopeId(&'static Scope);

impl std::cmp::PartialEq for ScopeId {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl std::cmp::Eq for ScopeId {}

impl fmt::Debug for ScopeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:p}", self.0)
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
