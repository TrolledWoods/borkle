use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::location::Location;
use crate::execution_time::ExecutionTime;
use crate::locals::LocalVariables;
use crate::operators::{BinaryOp, UnaryOp};
pub use crate::parser::{Node, NodeKind, Ast, NodeViewMut};
use crate::ast::NodeId;
use crate::program::{PolyOrMember, PolyMemberId, Program, Task, constant::ConstantRef, BuiltinFunction};
use crate::thread_pool::ThreadContext;
use crate::type_infer::{self, ValueId as TypeId, Args, TypeSystem, ValueSetId, TypeKind, Reason, ReasonKind};
use crate::types::{self, IntTypeKind};
use ustr::Ustr;

// type NodeViewMut<'a> = ast::GenericNodeView<'a, Attached<&'a mut [Node], &'a mut [ValueWrapper]>>;

#[derive(Clone)]
pub struct PolyParam {
    used_as_type: Option<Location>,
    used_as_value: Option<Location>,
    pub loc: Location,
    value_id: type_infer::ValueId,
}

impl PolyParam {
    fn is_type(&self) -> bool {
        self.used_as_type.is_some()
    }

    // Returns true on failure.
    fn check_for_dual_purpose(&self, errors: &mut ErrorCtx) -> bool {
        if let (Some(type_usage), Some(value_usage)) = (self.used_as_type, self.used_as_value) {
            errors.info(type_usage, "Used as a type here".to_string());
            errors.info(value_usage, "Used as a value here(to use types as values, you may need `type` before the generic)".to_string());
            errors.global_error("Used generic as both type and value".to_string());
            true
        } else {
            false
        }
    }
}

#[derive(Clone)]
pub struct YieldData {
    root_set_id: ValueSetId,
    root_value_id: type_infer::ValueId,
    locals: LocalVariables,
    ast: Ast,
    infer: TypeSystem,
    poly_params: Vec<PolyParam>,
    needs_explaining: Vec<(NodeId, type_infer::ValueId)>,
}

impl YieldData {
    pub fn insert_poly_params(&mut self, program: &Program, poly_args: &[(crate::types::Type, ConstantRef)]) {
        let set = self.root_set_id;

        for (param, &(compiler_type, constant)) in self.poly_params.iter().zip(poly_args) {
            if param.is_type() {
                debug_assert_eq!(compiler_type, types::Type::new(types::TypeKind::Type));
                let type_ = unsafe { *constant.as_ptr().cast::<types::Type>() };
                let type_id = self.infer.add_compiler_type(program, type_, set);

                self.infer.set_equal(param.value_id, type_id, Reason::temp_zero());
            } else {
                let type_ = self.infer.add_compiler_type(program, compiler_type, set);
                let value = self.infer.add_type(TypeKind::ConstantValue(constant), Args([]), set);
                let constant = self.infer.add_type(TypeKind::Constant, Args([(type_, Reason::temp_zero()), (value, Reason::temp_zero())]), set);

                self.infer.set_equal(constant, param.value_id, Reason::temp_zero());
            }
        }
    }
}

struct Context<'a, 'b> {
    thread_context: &'a mut ThreadContext<'b>,
    errors: &'a mut ErrorCtx,
    program: &'b Program,
    locals: &'a mut LocalVariables,
    /// Dependencies necessary for being able to emit code for this output.
    emit_deps: &'a mut DependencyList,
    infer: &'a mut TypeSystem,
    poly_params: &'a mut Vec<PolyParam>,
    runs: ExecutionTime,
    needs_explaining: &'a mut Vec<(NodeId, type_infer::ValueId)>,
}

pub fn process_ast<'a>(
    errors: &mut ErrorCtx,
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    locals: LocalVariables,
    ast: Ast,
) -> Result<Result<(DependencyList, LocalVariables, TypeSystem, Ast), (DependencyList, YieldData)>, ()> {
    let mut yield_data = begin(errors, thread_context, program, locals, ast, Vec::new());
    solve(errors, thread_context, program, &mut yield_data);
    finish(errors, yield_data)
}

pub fn begin<'a>(
    errors: &mut ErrorCtx,
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    mut locals: LocalVariables,
    mut ast: Ast,
    poly_params: Vec<(Location, Ustr)>,
) -> YieldData {
    let mut emit_deps = DependencyList::new();
    let mut infer = TypeSystem::new(program, ast.structure.len());

    let mut poly_params: Vec<_> = poly_params
        .into_iter()
        .map(|(loc, _)| {
            let value_id = infer.add_unknown_type();
            *infer.get_mut(value_id).is_base_value = true;

            PolyParam {
                loc,
                value_id,
                used_as_type: None,
                used_as_value: None,
            }
        })
        .collect();

    // Create type inference variables for all variables and nodes, so that there's a way to talk about
    // all of them.
    for local in locals.iter_mut() {
        local.type_infer_value_id = infer.add_unknown_type();
    }

    for label in locals.iter_labels_mut() {
        label.type_infer_value_id = infer.add_unknown_type();
    }

    let mut needs_explaining = Vec::new();
    let mut ctx = Context {
        thread_context,
        errors,
        program,
        locals: &mut locals,
        emit_deps: &mut emit_deps,
        poly_params: &mut poly_params,
        infer: &mut infer,
        runs: ExecutionTime::RuntimeFunc,
        needs_explaining: &mut needs_explaining,
    };

    // Build the type relationships between nodes.
    let root_set_id = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);
    let root_value_id = build_constraints(&mut ctx, ast.root_mut(), root_set_id);
    infer.value_sets.get_mut(root_set_id).emit_deps = Some(emit_deps);

    YieldData {
        root_set_id,
        root_value_id,
        ast,
        locals,
        infer,
        poly_params,
        needs_explaining,
    }
}

pub fn solve<'a>(
    errors: &mut ErrorCtx,
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    data: &mut YieldData,
) {
    let mut temp_emit_deps = DependencyList::new();
    let mut ctx = Context {
        thread_context,
        errors,
        program,
        locals: &mut data.locals,
        emit_deps: &mut temp_emit_deps,
        poly_params: &mut data.poly_params,
        infer: &mut data.infer,
        // This is only used in build_constraints, what it's set to doesn't matter
        runs: ExecutionTime::Never,
        needs_explaining: &mut data.needs_explaining,
    };

    loop {
        ctx.infer.solve();

        let mut progress = false;
        for value_set_id in ctx.infer.value_sets.iter_ids() {
            let value_set = ctx.infer.value_sets.get_mut(value_set_id);
            if value_set_id == 0 // <- Temporary from old things, we can deal with this case now, so do that!
            || value_set.has_errors
            || value_set.has_been_computed
            || value_set.uncomputed_values() > 0
            {
                continue;
            }

            debug_assert_eq!(value_set.uncomputed_values(), 0, "The number of uncomputed values cannot be less than zero");

            let related_nodes = std::mem::take(&mut value_set.related_nodes);
            for &node_id in &related_nodes {
                let mut node = data.ast.get_mut(node_id);
                if node.node.type_.is_none() {
                    node.type_ = Some(ctx.infer.value_to_compiler_type(TypeId::Node(node_id)));
                }
            }
            for local in ctx.locals.iter_mut() {
                if local.stack_frame_id == value_set_id {
                    debug_assert!(local.type_.is_none());
                    local.type_ = Some(ctx.infer.value_to_compiler_type(local.type_infer_value_id));
                }
            }
            let value_set = ctx.infer.value_sets.get_mut(value_set_id);
            value_set.related_nodes = related_nodes;
            value_set.has_been_computed = true;
            let waiting_on = std::mem::replace(&mut value_set.waiting_on_completion, WaitingOnTypeInferrence::None);

            subset_was_completed(&mut ctx, &mut data.ast, waiting_on, value_set_id);

            progress = true;
        }

        if !progress {
            break;
        }
    }

    debug_assert!(temp_emit_deps.is_empty(), "Didn't expect context to gain more emit_deps here, should clean up the code to not even have this case be possible");
}

pub fn finish<'a>(
    errors: &mut ErrorCtx,
    mut from: YieldData,
) -> Result<Result<(DependencyList, LocalVariables, TypeSystem, Ast), (DependencyList, YieldData)>, ()> {
    for (node_id, needs_explaining) in from.needs_explaining {
        for chain in type_infer::get_reasons(needs_explaining, &from.infer, &from.ast) {
            chain.output(errors, &from.ast, &from.infer);
            errors.note(from.ast.get(node_id).loc, format!("The type is `{}` because...", from.infer.value_to_str(needs_explaining, 0)));
        }
    }

    let mut are_incomplete_sets = false;
    for value_set_id in from.infer.value_sets.iter_ids() {
        let value_set = from.infer.value_sets.get(value_set_id);
        if value_set.has_errors || value_set.uncomputed_values() > 0 {
            errors.global_error(format!("Set {} is uncomputable! (uncomputability doesn't have a proper error yet, this is temporary)", value_set_id));
            are_incomplete_sets = true;
        }
    }

    if are_incomplete_sets | from.infer.output_errors(errors, &from.ast) {
        // from.infer.output_incompleteness_errors(errors, &from.poly_params, &from.ast, &from.locals);
        from.infer.flag_all_values_as_complete();
        return Err(());
    }

    for (i, node) in from.ast.nodes.iter_mut().enumerate() {
        if node.type_.is_none() {
            node.type_ = Some(from.infer.value_to_compiler_type(TypeId::Node(NodeId(i as u32))));
        }
    }

    for local in from.locals.iter_mut() {
        if local.type_.is_none() {
            local.type_ = Some(from.infer.value_to_compiler_type(local.type_infer_value_id));
        }
    }

    let emit_deps = from.infer.value_sets.get_mut(from.root_set_id).emit_deps.take().unwrap();

    Ok(Ok((emit_deps, from.locals, from.infer, from.ast)))
}

fn subset_was_completed(ctx: &mut Context<'_, '_>, ast: &mut Ast, waiting_on: WaitingOnTypeInferrence, set: ValueSetId) {
    match waiting_on {
        WaitingOnTypeInferrence::ConstantFromValueId { value_id, to, parent_set } => {
            // We expect the type to already be checked by some other mechanism,
            // e.g., node_type_id should be equal to the type of the constant.
            let constant_ref = ctx.infer.extract_constant_temp(value_id).unwrap();
            ast.get_mut(to).kind = NodeKind::Constant(constant_ref, None);
            ctx.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::TypeAsValue { type_id, node_id, parent_set } => {
            let compiler_type = ctx.infer.value_to_compiler_type(type_id);
            let constant_ref = ctx.program.insert_buffer(types::Type::new(types::TypeKind::Type), &compiler_type as *const _ as *const u8);
            ast.get_mut(node_id).kind = NodeKind::Constant(constant_ref, None);
            ctx.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::SizeOf { type_id, node_id, parent_set } => {
            let size = ctx.infer.get(type_id).layout.expect("This value is supposed to be complete").size;
            let constant_ref = ctx.program.insert_buffer(types::Type::new(types::TypeKind::Int(IntTypeKind::Usize)), &size as *const _ as *const u8);
            ast.get_mut(node_id).kind = NodeKind::Constant(constant_ref, None);
            ctx.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::MonomorphiseMember { node_id, poly_member_id, when_needed, params, parent_set } => {
            let node_loc = ast.get(node_id).loc;
            let mut fixed_up_params = Vec::with_capacity(params.len());

            for param in params {
                fixed_up_params.push(ctx.infer.extract_constant(ctx.program, param));
            }

            let wanted_dep = match when_needed {
                ExecutionTime::Typing => MemberDep::ValueAndCallableIfFunction,
                _ => MemberDep::Type,
            };

            ctx.infer.value_sets.unlock(parent_set);

            if let Ok(member_id) = ctx.program.monomorphise_poly_member(ctx.errors, ctx.thread_context, poly_member_id, &fixed_up_params, wanted_dep) {
                let (type_, meta_data) = ctx.program.get_member_meta_data(member_id);
                let compiler_type = ctx.infer.add_compiler_type(ctx.program, type_, parent_set);
                ctx.infer.set_equal(TypeId::Node(node_id), compiler_type, Reason::new(node_loc, ReasonKind::IsOfType));
                ast.get_mut(node_id).kind = NodeKind::ResolvedGlobal(member_id, meta_data.clone());

                match when_needed {
                    // This will never be emitted anyway so it doesn't matter if the value isn't accessible.
                    ExecutionTime::Never => {},
                    ExecutionTime::RuntimeFunc => {
                        let emit_deps = ctx.infer.value_sets.get_mut(parent_set).emit_deps.as_mut().unwrap();
                        emit_deps.add(node_loc, DepKind::Member(member_id, MemberDep::Value));
                    }
                    ExecutionTime::Emission => {
                        let emit_deps = ctx.infer.value_sets.get_mut(parent_set).emit_deps.as_mut().unwrap();
                        emit_deps.add(node_loc, DepKind::Member(member_id, MemberDep::ValueAndCallableIfFunction));
                    }
                    ExecutionTime::Typing => {
                        // The parser should have already made sure the value is accessible. We will run this node
                        // through the emitter anyway though, so we don't have to make it into a constant or something.
                    }
                }
            } else {
                ctx.infer.value_sets.get_mut(parent_set).has_errors |= true;
            }
        }
        WaitingOnTypeInferrence::ValueIdFromConstantComputation { computation, value_id } => {
            let len_loc = ast.get(computation).loc;
            match crate::interp::emit_and_run(
                ctx.thread_context,
                ctx.program,
                ctx.locals,
                ctx.infer,
                ast,
                computation,
                set,
                &mut vec![len_loc],
            ) {
                Ok(constant_ref) => {
                    let computation_node = ast.get(computation);
                    let finished_value = ctx.infer.add_value(TypeId::Node(computation), constant_ref, set);

                    ctx.infer.set_equal(finished_value, value_id, Reason::new(computation_node.loc, ReasonKind::IsOfType));
                }
                Err(call_stack) => {
                    for &caller in call_stack.iter().rev().skip(1) {
                        ctx.errors.info(caller, "".to_string());
                    }

                    ctx.errors.error(*call_stack.last().unwrap(), "Assert failed!".to_string());
                    ctx.infer.value_sets.get_mut(set).has_errors = true;
                }
            }
        }
        WaitingOnTypeInferrence::FunctionDeclaration {
            node_id,
            body,
            function_type,
            parent_set,
            time,
        } => {
            let node_loc = ast.get(node_id).loc;
            let function_id = ctx.program.insert_function(node_loc);

            let type_ = ctx.infer.value_to_compiler_type(function_type);
            let emit_deps = ctx.infer.value_sets.get_mut(set).emit_deps.take().unwrap();

            match time {
                ExecutionTime::Never => return,
                ExecutionTime::RuntimeFunc | ExecutionTime::Emission => {
                    let dependant_deps = ctx.infer.value_sets.get_mut(parent_set).emit_deps.as_mut().unwrap();
                    dependant_deps.add(node_loc, DepKind::Callable(function_id));

                    ctx.program.queue_task(
                        emit_deps,
                        Task::EmitFunction(
                            ctx.locals.clone(),
                            ctx.infer.clone(),
                            ast.clone(),
                            body,
                            type_,
                            function_id,
                            set,
                        ),
                    );
                }
                ExecutionTime::Typing => {
                    crate::emit::emit_function_declaration(
                        ctx.thread_context,
                        ctx.program,
                        ctx.locals,
                        ctx.infer,
                        ast,
                        body,
                        type_,
                        node_loc,
                        function_id,
                        set,
                    );
                }
            }

            let function_id_buffer = ctx
                .program
                .insert_buffer(type_, &function_id as *const _ as *const u8);

            // We are only allowed to change the node type here, because if this function declaration
            // is in a "polymorphic subtree"(that may be copied several times and use different types),
            // we need to become different functions.
            ast.get_mut(node_id).kind = NodeKind::Constant(
                function_id_buffer,
                None,
                // Later, we probably want the meta data for the function
                // included as well.
                /*Some(Arc::new(MemberMetaData::Function {
                    arg_names,
                    default_values,
                })),*/
            );

            ctx.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::BuiltinFunctionInTyping {
            node_id,
            function,
            type_,
            parent_set,
        } => {
            let node = ast.get_mut(node_id);
            let node_loc = node.loc;

            let type_ = ctx.infer.value_to_compiler_type(type_);

            let function_id = ctx.program.insert_defined_function(
                node_loc,
                Vec::new(),
                crate::ir::Routine::Builtin(function),
            );

            let types::TypeKind::Function { args, returns } = type_.kind() else { unreachable!("Defined as a function before, the type inferrence system is busted if this is reached") };

            // FIXME: This is duplicated in emit, could there be a nice way to deduplicate them?
            if ctx.program.arguments.release {
                crate::c_backend::function_declaration(
                    &mut ctx.thread_context.c_headers,
                    crate::c_backend::c_format_function(function_id),
                    args,
                    *returns,
                );

                ctx.thread_context.c_headers.push_str(";\n");

                crate::c_backend::function_declaration(
                    &mut ctx.thread_context.c_declarations,
                    crate::c_backend::c_format_function(function_id),
                    args,
                    *returns,
                );
                ctx.thread_context.c_declarations.push_str(" {\n");

                let routine = ctx.program.get_routine(function_id).unwrap();
                crate::c_backend::routine_to_c(
                    ctx.program,
                    &mut ctx.thread_context.c_declarations,
                    &routine,
                    args,
                    *returns,
                );
                ctx.thread_context.c_declarations.push_str("}\n");
            }

            ast.get_mut(node_id).kind = NodeKind::Constant(
                ctx.program.insert_buffer(type_, &function_id as *const _ as *const u8),
                None,
            );

            ctx.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::None => {},
    }
}

fn build_constraints(
    ctx: &mut Context<'_, '_>,
    mut node: NodeViewMut<'_>,
    set: ValueSetId,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(node.id);

    ctx.infer.set_value_set(node_type_id, set);
    ctx.infer.value_sets.add_node_to_set(set, node.id);

    match node.node.kind {
        NodeKind::Uninit | NodeKind::Zeroed => {}
        NodeKind::PolymorphicArgument(index) => {
            ctx.infer.value_sets.lock(set);

            let poly_param = &mut ctx.poly_params[index];
            poly_param.used_as_value.get_or_insert(node_loc);
            if poly_param.check_for_dual_purpose(ctx.errors) {
                ctx.infer.value_sets.get_mut(set).has_errors |= true;
            }

            let sub_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);
            let value_id = ctx.infer.add_value(node_type_id, (), sub_set);
            ctx.infer.set_equal(value_id, poly_param.value_id, Reason::new(node_loc, ReasonKind::Passed));

            ctx.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::ConstantFromValueId {
                value_id,
                to: node.id,
                parent_set: set,
            });
        }
        NodeKind::Explain => {
            let [inner] = node.children.into_array();
            let inner = build_constraints(ctx, inner, set);
            ctx.infer.set_equal(node_type_id, inner, Reason::new(node_loc, ReasonKind::Passed));
            ctx.needs_explaining.push((node.id, inner));
        }
        NodeKind::SizeOf => {
            let [inner] = node.children.into_array();
            let subset = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);
            let inner = build_type(ctx, inner, subset);

            ctx.infer.set_int(node_type_id, IntTypeKind::Usize, set);

            ctx.infer.value_sets.lock(set);
            ctx.infer.set_waiting_on_value_set(subset, WaitingOnTypeInferrence::SizeOf {
                type_id: inner,
                node_id: node.id,
                parent_set: set,
            });
        }
        NodeKind::Cast => {
            let [inner] = node.children.into_array();
            let result_value = build_constraints(ctx, inner, set);
            ctx.infer.set_cast(node_type_id, result_value, Reason::temp(node_loc));
        }
        NodeKind::BitCast => {
            let [value] = node.children.into_array();
            build_constraints(ctx, value, set);
        }
        NodeKind::Empty => {
            // @Performance: We could set the type directly(because no inferrence has happened yet),
            // this is a roundabout way of doing things.
            let temp = ctx.infer.add_type(type_infer::TypeKind::Empty, Args([]), set);
            ctx.infer.set_equal(node_type_id, temp, Reason::new(node_loc, ReasonKind::IsOfType));
        }
        NodeKind::PolymorphicArgs => {
            let mut children = node.children.into_iter();
            let on = children.next().unwrap();
            let &NodeKind::Global { scope, name } = &on.kind else {
                todo!("Handling of the case where you pass polymorphic args to something that shouldn't have it");
            };

            ctx.infer.set_value_set(TypeId::Node(on.id), set);
            ctx.infer.value_sets.add_node_to_set(set, on.id);
            ctx.infer.set_equal(TypeId::Node(on.id), node_type_id, Reason::temp(node_loc));

            let id = ctx.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");

            match id {
                PolyOrMember::Poly(id) => {
                    let num_args = ctx.program.get_num_poly_args(id);
                    let other_yield_data = ctx.program.get_polymember_yielddata(id);

                    let mut param_values = Vec::with_capacity(num_args);
                    let mut param_reasons = Vec::with_capacity(num_args);
                    let sub_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);

                    if num_args != children.len() {
                        ctx.errors.error(node_loc, format!("Passed {} arguments to polymorphic value, but the polymorphic value needs {} values", children.len(), num_args));
                        // @Cleanup: This should probably just be a function on TypeSystem
                        ctx.infer.value_sets.get_mut(set).has_errors |= true;
                        return node_type_id;
                    }

                    for (i, (param, other_poly_arg)) in children.zip(&other_yield_data.poly_params).enumerate() {
                        let param_loc = param.loc;
                        if other_poly_arg.is_type() {
                            let type_id = build_type(ctx, param, sub_set);
                            param_values.push(type_id);
                            param_reasons.push((type_id, other_poly_arg.value_id, Reason::new(param_loc, ReasonKind::PolyParam(i))));
                        } else {
                            let (_, param_value_id) = build_inferrable_constant_value(ctx, param, sub_set);
                            param_values.push(param_value_id);
                            param_reasons.push((param_value_id, other_poly_arg.value_id, Reason::new(param_loc, ReasonKind::PolyParam(i))));
                        }
                    }

                    param_reasons.push((node_type_id, other_yield_data.root_value_id, Reason::new(node_loc, ReasonKind::PolyMember(id))));

                    ctx.infer.add_subtree_from_other_typesystem(
                        &other_yield_data.infer, 
                        param_reasons.into_iter(),
                        // This should technically not need a set, because nothing depends on this, it's just some
                        // scaffolding to allow the things that people depend on to be inferred.
                        sub_set,
                    );

                    ctx.infer.value_sets.lock(set);

                    ctx.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::MonomorphiseMember {
                        node_id: node.id,
                        poly_member_id: id,
                        when_needed: ctx.runs,
                        params: param_values,
                        parent_set: set,
                    });
                }
                PolyOrMember::Member(id) => {
                    if children.len() > 0 {
                        // This is an error, since it's not polymorphic
                        ctx.errors.error(node_loc, "Passed polymorphic parameters even though this value isn't polymorphic".to_string());
                        // @Cleanup: This should probably just be a function on TypeSystem
                        ctx.infer.value_sets.get_mut(set).has_errors |= true;
                        return node_type_id;
                    }

                    let (type_, meta_data) = ctx.program.get_member_meta_data(id);

                    let type_id = ctx.infer.add_compiler_type(
                        ctx.program,
                        type_,
                        set,
                    );

                    ctx.infer.set_equal(node_type_id, type_id, Reason::new(node_loc, ReasonKind::IsOfType));

                    match ctx.runs {
                        // This will never be emitted anyway so it doesn't matter if the value isn't accessible.
                        ExecutionTime::Never => {},
                        ExecutionTime::RuntimeFunc => {
                            ctx.emit_deps.add(node_loc, DepKind::Member(id, MemberDep::Value));
                        }
                        ExecutionTime::Emission => {
                            ctx.emit_deps.add(node_loc, DepKind::Member(id, MemberDep::ValueAndCallableIfFunction));
                        }
                        ExecutionTime::Typing => {
                            // The parser should have already made sure the value is accessible. We will run this node
                            // through the emitter anyway though, so we don't have to make it into a constant or something.
                        }
                    }

                    node.node.kind = NodeKind::ResolvedGlobal(id, meta_data);
                }
            }
    
        }
        // @Cleanup: We could unify these two nodes probably
        NodeKind::Global { scope, name } => {
            let id = ctx.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");

            match id {
                PolyOrMember::Poly(id) => {
                    let num_args = ctx.program.get_num_poly_args(id);
                    let other_yield_data = ctx.program.get_polymember_yielddata(id);

                    let mut param_values = Vec::with_capacity(num_args);
                    let mut param_reasons = Vec::with_capacity(num_args);
                    let sub_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);

                    for (i, other_poly_arg) in other_yield_data.poly_params.iter().enumerate() {
                        let param_value_id = ctx.infer.add_unknown_type_with_set(sub_set);
                        param_values.push(param_value_id);
                        param_reasons.push((param_value_id, other_poly_arg.value_id, Reason::new(node_loc, ReasonKind::InferredPolyParam(i))));
                    }

                    param_reasons.push((node_type_id, other_yield_data.root_value_id, Reason::new(node_loc, ReasonKind::PolyMember(id))));

                    ctx.infer.add_subtree_from_other_typesystem(
                        &other_yield_data.infer, 
                        param_reasons.into_iter(),
                        // This should technically not need a set, because nothing depends on this, it's just some
                        // scaffolding to allow the things that people depend on to be inferred.
                        sub_set,
                    );

                    ctx.infer.value_sets.lock(set);

                    ctx.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::MonomorphiseMember {
                        node_id: node.id,
                        poly_member_id: id,
                        when_needed: ctx.runs,
                        params: param_values,
                        parent_set: set,
                    });
                }
                PolyOrMember::Member(id) => {
                    let (type_, meta_data) = ctx.program.get_member_meta_data(id);

                    let type_id = ctx.infer.add_compiler_type(
                        ctx.program,
                        type_,
                        set,
                    );

                    ctx.infer.set_equal(node_type_id, type_id, Reason::new(node_loc, ReasonKind::IsOfType));

                    match ctx.runs {
                        // This will never be emitted anyway so it doesn't matter if the value isn't accessible.
                        ExecutionTime::Never => {},
                        ExecutionTime::RuntimeFunc => {
                            ctx.emit_deps.add(node_loc, DepKind::Member(id, MemberDep::Value));
                        }
                        ExecutionTime::Emission => {
                            ctx.emit_deps.add(node_loc, DepKind::Member(id, MemberDep::ValueAndCallableIfFunction));
                        }
                        ExecutionTime::Typing => {
                            // The parser should have already made sure the value is accessible. We will run this node
                            // through the emitter anyway though, so we don't have to make it into a constant or something.
                        }
                    }

                    node.kind = NodeKind::ResolvedGlobal(id, meta_data);
                }
            }
        }
        NodeKind::While {
            iteration_var,
            label,
        } => {
            let [condition, body, else_body] = node.children.into_array();

            ctx.locals.get_mut(iteration_var).stack_frame_id = set;
            ctx.locals.get_label_mut(label).stack_frame_id = set;

            ctx.infer.set_int(ctx.locals.get(iteration_var).type_infer_value_id, IntTypeKind::Usize, set);

            let condition_type_id = build_constraints(ctx, condition, set);
            let bool_type = ctx.infer.add_type(TypeKind::Bool, Args([]), set);
            ctx.infer.set_equal(condition_type_id, bool_type, Reason::new(node_loc, ReasonKind::IsOfType));

            let label_type_infer_id = ctx.locals.get_label(label).type_infer_value_id;

            build_constraints(ctx, body, set);

            let else_type = build_constraints(ctx, else_body, set);
            ctx.infer.set_equal(label_type_infer_id, else_type, Reason::new(node_loc, ReasonKind::Passed));

            ctx.infer.set_equal(node_type_id, label_type_infer_id, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::For {
            iterator,
            iteration_var,
            label,
        } => {
            let [iterating, body, else_body] = node.children.into_array();

            ctx.locals.get_mut(iteration_var).stack_frame_id = set;
            ctx.locals.get_mut(iterator).stack_frame_id = set;
            ctx.locals.get_label_mut(label).stack_frame_id = set;

            ctx.infer.set_int(ctx.locals.get(iteration_var).type_infer_value_id, IntTypeKind::Usize, set);

            // The type the body returns doesn't matter, since we don't forward it.
            let iterating_type_id = build_constraints(ctx, iterating, set);

            build_constraints(ctx, body, set);

            let label_type_infer_id = ctx.locals.get_label(label).type_infer_value_id;

            ctx.infer.set_for_relation(ctx.locals.get(iterator).type_infer_value_id, iterating_type_id, Reason::temp(node_loc));

            let else_type = build_constraints(ctx, else_body, set);
            ctx.infer.set_equal(label_type_infer_id, else_type, Reason::new(node_loc, ReasonKind::Passed));

            ctx.infer.set_equal(node_type_id, label_type_infer_id, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::Literal(Literal::Int(_)) => {
            ctx.infer.set_type(node_type_id, TypeKind::Int, (), set);
        }
        NodeKind::Defer => {
            let [deferring] = node.children.into_array();
            build_constraints(ctx, deferring, set);
            let empty_id = ctx.infer.add_type(
                TypeKind::Empty, Args([]),
                set,
            );

            ctx.infer.set_equal(node_type_id, empty_id, Reason::new(node_loc, ReasonKind::IsOfType));
        }
        NodeKind::Literal(Literal::String(ref data)) => {
            let u8_type = ctx.infer.add_int(IntTypeKind::U8, set);
            ctx.infer.set_type(node_type_id, TypeKind::Buffer, Args([(u8_type, Reason::temp(node_loc))]), set);

            let u8_type = types::Type::new(types::TypeKind::Int(IntTypeKind::U8));
            let type_ = types::Type::new(types::TypeKind::Buffer { pointee: u8_type });
            let ptr = ctx.program.insert_buffer(
                type_,
                &crate::types::BufferRepr {
                    ptr: data.as_ptr() as *mut _,
                    length: data.len(),
                } as *const _ as *const _,
            );
            node.kind = NodeKind::Constant(ptr, None);
        }
        NodeKind::BuiltinFunction(function) => {
            let function_type_id = ctx.infer.add_unknown_type();
            let sub_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::BuiltinFunctionInTyping {
                node_id: node.id,
                function,
                type_: function_type_id,
                parent_set: set,
            });

            // The parent value set has to wait for this function declaration to be emitted until
            // it can continue, so we lock it to make sure it doesn't get emitted before then.
            ctx.infer.value_sets.lock(set);

            ctx.infer.set_type(function_type_id, TypeKind::Function, (), sub_set);
            ctx.infer.set_equal(node_type_id, function_type_id, Reason::new(node_loc, ReasonKind::IsOfType));
        }
        NodeKind::ArrayLiteral => {
            let inner_type = ctx.infer.add_unknown_type_with_set(set);

            for arg in node.children.iter() {
                let arg_type_id = build_constraints(ctx, arg, set);
                ctx.infer.set_equal(arg_type_id, inner_type, Reason::new(node_loc, ReasonKind::Passed));
            }

            let usize = ctx.infer.add_int(IntTypeKind::Usize, set);
            let length = ctx.program.insert_buffer(types::Type::new(types::TypeKind::Int(IntTypeKind::Usize)), (node.children.len()).to_le_bytes().as_ptr());

            let variable_count = ctx.infer.add_value(
                usize,
                length,
                set,
            );

            let array_type = ctx.infer.add_type(
                TypeKind::Array, Args([(inner_type, Reason::temp(node_loc)), (variable_count, Reason::temp(node_loc))]),
                set,
            );

            ctx.infer.set_equal(node_type_id, array_type, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::Member { name } => {
            let [of] = node.children.into_array();
            let of_type_id = build_constraints(ctx, of, set);
            ctx.infer
                .set_field_name_equal(of_type_id, name, node_type_id, Reason::new(node_loc, ReasonKind::NamedField(name)));
        }
        NodeKind::Local(local_id) => {
            let local = ctx.locals.get(local_id);
            let local_type_id = local.type_infer_value_id;
            ctx.infer
                .set_equal(local_type_id, node_type_id, Reason::new(node_loc, ReasonKind::LocalVariableIs(local.name)));

            if ctx.runs != ExecutionTime::Never && local.stack_frame_id != set {
                dbg!(local.stack_frame_id);
                ctx.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type". to_string());
                ctx.infer.value_sets.get_mut(set).has_errors = true;
            }
        }
        NodeKind::If {
            is_const: _,
        } => {
            let [condition, true_body, else_body] = node.children.into_array();
            let condition_type_id = build_constraints(ctx, condition, set);
            // @Performance: This could be better, I really want a constraint for this kind of thing...
            let condition_type = ctx.infer.add_type(TypeKind::Bool, Args([]), set);
            ctx.infer
                .set_equal(condition_type_id, condition_type, Reason::new(node_loc, ReasonKind::IsOfType));

            let true_body_id = build_constraints(ctx, true_body, set);
            let false_body_id = build_constraints(ctx, else_body, set);

            ctx.infer
                .set_equal(true_body_id, node_type_id, Reason::new(node_loc, ReasonKind::Passed));
            ctx.infer
                .set_equal(false_body_id, node_type_id, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            let [operand] = node.children.into_array();
            let operand_type_id = build_constraints(ctx, operand, set);

            let temp = ctx.infer.add_type(
                TypeKind::Reference,
                Args([(node_type_id, Reason::new(node_loc, ReasonKind::Dereference))]),
                set,
            );
            ctx.infer
                .set_equal(operand_type_id, temp, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::FunctionDeclaration { ref args } => {
            let mut emit_deps = DependencyList::new();

            let mut sub_ctx = Context {
                thread_context: ctx.thread_context,
                errors: ctx.errors,
                program: ctx.program,
                locals: ctx.locals,
                emit_deps: &mut emit_deps,
                poly_params: ctx.poly_params,
                infer: ctx.infer,
                needs_explaining: ctx.needs_explaining,
                runs: ctx.runs.combine(ExecutionTime::RuntimeFunc),
            };

            let sub_set = sub_ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);

            // The parent value set has to wait for this function declaration to be emitted until
            // it can continue, so we lock it to make sure it doesn't get emitted before then.
            sub_ctx.infer.value_sets.lock(set);

            let mut function_type_ids = Vec::with_capacity(args.len() + 1);
            let mut children = node.children.iter();
            let num_children = children.len();
            for (&local_id, type_node) in args.iter().zip(children.by_ref().take(num_children - 2)) {
                let local = sub_ctx.locals.get_mut(local_id);
                let name = local.name;
                local.stack_frame_id = sub_set;
                let local_type_id = local.type_infer_value_id;
                sub_ctx.infer.set_value_set(local_type_id, sub_set);

                let type_node_loc = type_node.loc;
                let type_id = build_type(&mut sub_ctx, type_node, sub_set);
                sub_ctx.infer
                    .set_equal(type_id, local_type_id, Reason::new(type_node_loc, ReasonKind::FunctionDeclArgumentType(name)));

                function_type_ids.push((local_type_id, Reason::new(node_loc, ReasonKind::FunctionDeclArgumentDeclaration(name))));
            }

            let returns = children.next().unwrap();
            let returns_type_reason = Reason::new(returns.loc, ReasonKind::FunctionDeclReturnType);
            let returns_loc = returns.loc;
            let returns_type_id = build_type(&mut sub_ctx, returns, sub_set);
            function_type_ids.insert(0, (returns_type_id, returns_type_reason));

            let body = children.next().unwrap();
            let body_id = body.id;
            let body_type_id = build_constraints(&mut sub_ctx, body, sub_set);

            ctx.infer
                .set_equal(body_type_id, returns_type_id, Reason::new(returns_loc, ReasonKind::FunctionDeclReturned));

            let infer_type_id = ctx.infer.add_type(TypeKind::Function, Args(function_type_ids), sub_set);
            ctx.infer
                .set_equal(infer_type_id, node_type_id, Reason::new(node_loc, ReasonKind::FunctionDecl));

            ctx.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::FunctionDeclaration {
                node_id: node.id,
                body: body_id,
                function_type: infer_type_id,
                parent_set: set,
                time: ctx.runs,
            });
            let old_set = ctx.infer.value_sets.get_mut(sub_set).emit_deps.replace(emit_deps);
            debug_assert!(old_set.is_none());
        }
        NodeKind::FunctionCall => {
            let mut children = node.children.into_iter();
            let calling = children.next().unwrap();
            let calling_type_id = build_constraints(ctx, calling, set);

            // A little bit hacky, but since we are invariant to the return type
            // (variance is always applied before merges of types essentially, and this is the creation of a type),
            // we can get away with this.
            let return_type = node_type_id;

            let mut typer_args = Vec::with_capacity(children.len());
            typer_args.push((return_type, Reason::new(node_loc, ReasonKind::FunctionCallReturn)));

            let num_args = children.len();
            for arg in children {
                let function_arg_type_id = ctx.infer.add_unknown_type();
                let arg_type_id = build_constraints(ctx, arg, set);
                ctx.infer.set_equal(function_arg_type_id, arg_type_id, Reason::new(node_loc, ReasonKind::Passed));
                typer_args.push((function_arg_type_id, Reason::new(node_loc, ReasonKind::FunctionCallArgument)));
            }

            // Specify that the caller has to be a function type
            let type_id = ctx.infer.add_type(TypeKind::Function, Args(typer_args), set);
            ctx.infer
                .set_equal(calling_type_id, type_id, Reason::new(node_loc, ReasonKind::FunctionCall));

            node.node.kind = NodeKind::ResolvedFunctionCall {
                arg_indices: (0..num_args).collect(),
            };
        }
        NodeKind::Declare {
            local,
        } => {
            let [value] = node.children.into_array();
            // Set the set of the local to this type set
            let local = ctx.locals.get_mut(local);
            local.stack_frame_id = set;
            ctx.infer.set_value_set(local.type_infer_value_id, set);
            let local_type_id = local.type_infer_value_id;

            let right_type_id = build_constraints(ctx, value, set);

            ctx.infer
                .set_equal(local_type_id, right_type_id, Reason::new(node_loc, ReasonKind::Declaration));

            ctx.infer.set_type(
                node_type_id,
                TypeKind::Empty, Args([]),
                set,
            );
        }
        NodeKind::Binary {
            op: BinaryOp::Assign,
        } => {
            let [left, right] = node.children.into_array();
            let left_type_id = build_lvalue(ctx, left, set);
            let right_type_id = build_constraints(ctx, right, set);

            ctx.infer
                .set_equal(left_type_id, right_type_id, Reason::new(node_loc, ReasonKind::Assigned));

            ctx.infer.set_type(
                node_type_id,
                TypeKind::Empty, Args([]),
                set,
            );
        }
        NodeKind::Binary { op } => {
            let [left, right] = node.children.into_array();
            let left = build_constraints(ctx, left, set);
            let right = build_constraints(ctx, right, set);
            ctx.infer.set_op_equal(op, left, right, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::Reference => {
            let [operand] = node.children.into_array();
            let inner = build_lvalue(ctx, operand, set);
            ctx.infer.set_type(
                node_type_id,
                TypeKind::Reference,
                Args([(inner, Reason::temp(node_loc))]),
                set,
            );
        }
        NodeKind::Block {
            label,
        } => {
            if let Some(label) = label {
                let label = ctx.locals.get_label_mut(label);
                ctx.infer.set_equal(label.type_infer_value_id, node_type_id, Reason::temp(node_loc));
                label.stack_frame_id = set;
            }

            // @Performance: This isn't very fast, but it's fine for now
            let mut children = node.children.into_iter();
            let children_len = children.len();
            for statement_id in children.by_ref().take(children_len - 1) {
                build_constraints(ctx, statement_id, set);
            }

            let last_type_id = build_constraints(ctx, children.next().unwrap(), set);
            ctx.infer
                .set_equal(node_type_id, last_type_id, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::Break {
            label,
            num_defer_deduplications: _,
        } => {
            let [value] = node.children.into_array();

            let label = ctx.locals.get_label(label);
            if ctx.runs != ExecutionTime::Never && label.stack_frame_id != set {
                ctx.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type".to_string());
                ctx.infer.value_sets.get_mut(set).has_errors = true;
            }

            let label_type_id = label.type_infer_value_id;

            let value_type_id = build_constraints(ctx, value, set);
            ctx.infer.set_equal(value_type_id, label_type_id, Reason::temp(node_loc));

            ctx.infer.set_type(
                node_type_id,
                TypeKind::Empty, Args([]),
                set,
            );
        }
        NodeKind::Parenthesis => {
            let [inner] = node.children.into_array();
            let inner_type_id = build_constraints(ctx, inner, set);
            ctx.infer
                .set_equal(inner_type_id, node_type_id, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::TypeAsValue => {
            let [inner] = node.children.into_array();
            let old_runs = ctx.runs;
            ctx.runs = ctx.runs.combine(ExecutionTime::Typing);
            let subset = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);
            let type_id = build_type(ctx, inner, subset);

            ctx.infer.value_sets.lock(set);
            ctx.infer.set_waiting_on_value_set(subset, WaitingOnTypeInferrence::TypeAsValue {
                type_id,
                node_id: node.id,
                parent_set: set,
            });
            
            ctx.infer.set_type(node_type_id, TypeKind::Type, Args([]), set);
            ctx.runs = old_runs;
        }
        NodeKind::TypeBound => {
            let [value, bound] = node.children.into_array();
            let value_type_id = build_constraints(ctx, value, set);
            let bound_type_id = build_type(ctx, bound, set);
            ctx.infer
                .set_equal(node_type_id, bound_type_id, Reason::new(node_loc, ReasonKind::TypeBound));
            ctx.infer
                .set_equal(value_type_id, node_type_id, Reason::new(node_loc, ReasonKind::Passed));
        }
        _ => unimplemented!(
            "Ast node does not have a typing relationship yet {:?}",
            node.kind
        ),
    }

    node_type_id
}

fn build_type(
    ctx: &mut Context<'_, '_>,
    node: NodeViewMut<'_>,
    set: ValueSetId,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(node.id);

    ctx.infer.set_value_set(node_type_id, set);
    ctx.infer.value_sets.add_node_to_set(set, node.id);

    match node.kind {
        NodeKind::ImplicitType => {},
        NodeKind::PolymorphicArgument(index) => {
            let poly_param = &mut ctx.poly_params[index];
            poly_param.used_as_type.get_or_insert(node_loc);
            if poly_param.check_for_dual_purpose(ctx.errors) {
                ctx.infer.value_sets.get_mut(set).has_errors |= true;
            }
            ctx.infer.set_equal(poly_param.value_id, node_type_id, Reason::temp(node_loc));
        }
        // @Cleanup: I don't really want TypeAsValue here, but since the typer has more information than the parser
        // the parser might need it as a "hint", so until type expressions and normal values have the same syntax,
        // this'll have to do.
        NodeKind::Parenthesis | NodeKind::TypeAsValue => {
            let [inner] = node.children.into_array();
            let inner_type_id = build_type(ctx, inner, set);
            ctx.infer
                .set_equal(inner_type_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::LiteralType(type_) => {
            ctx.infer.set_compiler_type(ctx.program, node_type_id, type_, set);
        }
        NodeKind::FunctionType => {
            let mut children = node.children.into_iter();
            let mut function_type_ids = Vec::with_capacity(children.len());
            let num_children = children.len();
            for type_node in children.by_ref().take(num_children - 1) {
                let type_id = build_type(ctx, type_node, set);
                function_type_ids.push((type_id, Reason::temp(node_loc)));
            }

            let returns_type_id = build_type(ctx, children.next().unwrap(), set);
            function_type_ids.insert(0, (returns_type_id, Reason::temp(node_loc)));

            let infer_type_id = ctx.infer.add_type(TypeKind::Function, Args(function_type_ids), set);
            ctx.infer
                .set_equal(infer_type_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::StructType { ref fields } => {
            // @Performance: Many allocations
            let names = fields.to_vec().into_boxed_slice();
            let fields: Vec<_> = node.children.into_iter().map(|v| (build_type(ctx, v, set), Reason::temp(node_loc))).collect();
            ctx.infer.set_type(node_type_id, TypeKind::Struct(names), Args(fields), set);
        }
        NodeKind::ReferenceType => {
            let [inner] = node.children.into_array();
            let inner = build_type(ctx, inner, set);
            ctx.infer.set_type(
                node_type_id,
                TypeKind::Reference, Args([(inner, Reason::temp(node_loc))]),
                set,
            );
        }
        NodeKind::BufferType => {
            let [inner] = node.children.into_array();
            let inner = build_type(ctx, inner, set);
            ctx.infer.set_type(
                node_type_id,
                TypeKind::Buffer, Args([(inner, Reason::temp(node_loc))]),
                set,
            );
        }
        NodeKind::ArrayType => {
            let [len, members] = node.children.into_array();
            let (length_type, length_value) = build_inferrable_constant_value(ctx, len, set);
            let usize_type = ctx.infer.add_int(IntTypeKind::Usize, set);
            ctx.infer.set_equal(usize_type, length_type, Reason::temp(node_loc));

            let member_type_id = build_type(ctx, members, set);
            ctx.infer.set_type(node_type_id, TypeKind::Array, Args([(member_type_id, Reason::temp(node_loc)), (length_value, Reason::temp(node_loc))]), set);
        }
        NodeKind::TypeOf => {
            let [inner] = node.children.into_array();
            let old = ctx.runs;
            ctx.runs = ctx.runs.combine(ExecutionTime::Never);
            let type_ = build_constraints(ctx, inner, set);
            ctx.runs = old;
            ctx.infer.set_equal(node_type_id, type_, Reason::new(node_loc, ReasonKind::TypeOf));
        }
        _ => unreachable!("Node {:?} is not a valid type (at least not yet)", node.kind),
    }

    node_type_id
}

/// Normal values are assumed to be readonly, because they are temporaries, it doesn't really make sense to
/// write to them. However, in some cases the value isn't a temporary at all, but actually refers to a value
/// inside of another value. That's what this is for. Instead of forcing the value to be readonly, we can make
/// the readability/writability of the value depend on deeper values in the expression.
/// If this strategy doesn't work however, we fallback to read-only.
fn build_lvalue(
    ctx: &mut Context<'_, '_>,
    node: NodeViewMut<'_>,
    set: ValueSetId,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(node.id);

    match node.kind {
        NodeKind::Member { name } => {
            let [of] = node.children.into_array();
            let of_type_id = build_lvalue(ctx, of, set);
            ctx.infer
                .set_field_name_equal(of_type_id, name, node_type_id, Reason::new(node_loc, ReasonKind::NamedField(name)));
        }
        NodeKind::Local(local_id) => {
            let local = ctx.locals.get(local_id);
            let local_type_id = local.type_infer_value_id;
            ctx.infer
                .set_equal(local_type_id, node_type_id, Reason::new(node_loc, ReasonKind::LocalVariableIs(local.name)));

            if local.stack_frame_id != set {
                ctx.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type".to_string());
                ctx.infer.value_sets.get_mut(set).has_errors = true;
            }
        }
        NodeKind::Parenthesis => {
            let [value] = node.children.into_array();
            let inner = build_lvalue(ctx, value, set);
            ctx.infer.set_equal(node_type_id, inner, Reason::temp(node_loc));
        }
        NodeKind::TypeBound => {
            let [value, bound] = node.children.into_array();
            // @Improvment: Here, both things are invariant. One of them could potentially be variant,
            // but only in some cases. After I think about how cases like this actually work,
            // I could try integrating this variance with the `access` variance passed in here to make it
            // less restrictive. It would also be nice if it was consistant with how non lvalue typebounds work,
            // since right now that's an inconsistancy that's going to be weird if you trigger it.
            let bound_type_id = build_type(ctx, bound, set);
            ctx.infer
                .set_equal(node_type_id, bound_type_id, Reason::temp(node_loc));
            let value_type_id = build_lvalue(ctx, value, set);
            ctx.infer
                .set_equal(value_type_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            let [operand] = node.children.into_array();

            let temp = ctx.infer.add_type(
                TypeKind::Reference,
                Args([(node_type_id, Reason::temp(node_loc))]),
                set,
            );

            let operand_type_id = build_constraints(ctx, operand, set);
            ctx.infer
                .set_equal(operand_type_id, temp, Reason::temp(node_loc));
        }
        _ => {
            // Make it a reference to a temporary instead. This forces the pointer to be readonly.
            // TODO: Make it require it to be read-only here.
            return build_constraints(ctx, node, set);
        }
    }

    ctx.infer.set_value_set(node_type_id, set);
    ctx.infer.value_sets.add_node_to_set(set, node.id);

    node_type_id
}

// The first return is the type of the constant, the second return is the value id of that constant, where the constant will later be stored.
fn build_inferrable_constant_value(
    ctx: &mut Context<'_, '_>,
    node: NodeViewMut<'_>,
    set: ValueSetId,
) -> (type_infer::ValueId, type_infer::ValueId) {
    let node_loc = node.loc;
    let node_id = node.id;
    let node_type_id = TypeId::Node(node.id);

    let value_id = match node.kind {
        NodeKind::PolymorphicArgument(index) => {
            let value_id = ctx.infer.add_value(node_type_id, (), set);
            let poly_param = &mut ctx.poly_params[index];
            poly_param.used_as_value.get_or_insert(node_loc);
            if poly_param.check_for_dual_purpose(ctx.errors) {
                ctx.infer.value_sets.get_mut(set).has_errors |= true;
            }
            ctx.infer.set_equal(poly_param.value_id, value_id, Reason::temp(node_loc));
            value_id
        }
        NodeKind::ImplicitType => {
            // Nothing at all is known about it, _except_ that the type of this node is equal to the
            // value.
            ctx.infer.add_value(node_type_id, (), set)
        }
        _ => {
            // We can't figure it out in a clever way, so just compile time execute the node as a constant.
            let mut sub_ctx = Context {
                thread_context: ctx.thread_context,
                errors: ctx.errors,
                program: ctx.program,
                locals: ctx.locals,
                emit_deps: ctx.emit_deps,
                poly_params: ctx.poly_params,
                infer: ctx.infer,
                runs: ctx.runs.combine(ExecutionTime::Typing),
                needs_explaining: ctx.needs_explaining,
            };
            let sub_set = sub_ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);

            let constant_type_id = build_constraints(&mut sub_ctx, node, sub_set);
            let value_id = ctx.infer.add_value(constant_type_id, (), set);
            ctx.infer.set_equal(node_type_id, constant_type_id, Reason::temp(node_loc));

            ctx.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::ValueIdFromConstantComputation {
                computation: node_id,
                value_id,
            });

            // Because the set of the node is already set by build_constraints, we early return type
            // @HACK because rust lints are BS
            if (|| true)() {
                return (node_type_id, value_id);
            }

            value_id
        }
    };

    ctx.infer.set_value_set(node_type_id, set);
    ctx.infer.value_sets.add_node_to_set(set, node_id);

    (node_type_id, value_id)
}

pub fn explain_given_type(ast: &Ast, node_id: NodeId) -> Reason {
    let node_loc = ast.get(node_id).loc;
    match ast.get(node_id).kind {
        NodeKind::LiteralType(_) => Reason::new(node_loc, ReasonKind::LiteralType),
        NodeKind::Literal(Literal::Int(_)) => Reason::new(node_loc, ReasonKind::IntLiteral),
        _ => Reason::temp(node_loc),
    }
}

#[derive(Clone)]
pub enum WaitingOnTypeInferrence {
    TypeAsValue {
        type_id: type_infer::ValueId,
        node_id: NodeId,
        parent_set: ValueSetId,
    },
    SizeOf {
        type_id: type_infer::ValueId,
        node_id: NodeId,
        parent_set: ValueSetId,
    },
    MonomorphiseMember {
        node_id: NodeId,
        poly_member_id: PolyMemberId,
        when_needed: ExecutionTime,
        params: Vec<type_infer::ValueId>,
        parent_set: ValueSetId,
    },
    FunctionDeclaration {
        node_id: NodeId,
        body: NodeId,
        function_type: TypeId,
        /// This is because function declaration create a constant in the
        /// parent set, and we have to make sure that the parent set isn't
        /// emitted before that constant is created.
        parent_set: ValueSetId,
        time: ExecutionTime,
    },
    BuiltinFunctionInTyping {
        node_id: NodeId,
        function: BuiltinFunction,
        type_: TypeId,
        parent_set: ValueSetId,
    },
    ConstantFromValueId {
        value_id: type_infer::ValueId,
        to: NodeId,
        parent_set: ValueSetId,
    },
    ValueIdFromConstantComputation {
        computation: NodeId,
        value_id: type_infer::ValueId,
    },
    None,
}
