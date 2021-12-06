use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::execution_time::ExecutionTime;
use crate::locals::LocalVariables;
use crate::operators::{BinaryOp, UnaryOp};
pub use crate::parser::{ast::Node, ast::NodeId, ast::NodeKind, Ast};
use crate::program::{PolyOrMember, PolyMemberId, Program, Task, constant::ConstantRef, FunctionId, BuiltinFunction};
use crate::thread_pool::ThreadContext;
use crate::type_infer::{self, ValueId as TypeId, TypeSystem, ValueSetId, Variance, TypeKind};
use crate::types::{self, IntTypeKind, PtrPermits};

#[derive(Clone)]
pub struct YieldData {
    emit_deps: DependencyList,
    locals: LocalVariables,
    ast: Ast,
    infer: TypeSystem,
    poly_param_usages: Vec<(usize, TypeId, NodeId, ValueSetId)>,
}

impl YieldData {
    pub fn insert_poly_params(&mut self, poly_args: &[(crate::types::Type, ConstantRef)]) {
        // @HACK: For now, we just use the value set 0
        let set = 0;
        let type_values: Vec<_> = poly_args.iter().map(|&(v, _)| self.infer.add_compiler_type(v, set)).collect();

        for (arg_id, value_id, node_id, set_id) in self.poly_param_usages.drain(..) {
            self.infer.set_polymorph_value(value_id, type_values[arg_id]);

            self.ast.get_mut(node_id).kind = NodeKind::Constant(poly_args[arg_id].1, None);
            self.infer.value_sets.unlock(set_id);
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
    ast: &'a mut Ast,
    infer: &'a mut TypeSystem,
    poly_param_usages: &'a mut Vec<(usize, TypeId, NodeId, ValueSetId)>,
    runs: ExecutionTime,
}

pub fn process_ast<'a>(
    errors: &mut ErrorCtx,
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    locals: LocalVariables,
    ast: Ast,
) -> Result<Result<(DependencyList, LocalVariables, TypeSystem, Ast), (DependencyList, YieldData)>, ()> {
    let mut yield_data = begin(errors, thread_context, program, locals, ast);
    solve(errors, thread_context, program, &mut yield_data);
    finish(errors, yield_data)
}

pub fn begin<'a>(
    errors: &mut ErrorCtx,
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    mut locals: LocalVariables,
    mut ast: Ast,
) -> YieldData {
    let mut emit_deps = DependencyList::new();
    let mut infer = TypeSystem::new(program);
    let mut poly_param_usages = Vec::new();

    // Create type inference variables for all variables and nodes, so that there's a way to talk about
    // all of them.
    for node in &mut ast.nodes {
        node.type_infer_value_id = infer.add_unknown_type();
    }

    for local in locals.iter_mut() {
        local.type_infer_value_id = infer.add_unknown_type();
    }

    for label in locals.iter_labels_mut() {
        label.type_infer_value_id = infer.add_unknown_type();
    }

    let mut ctx = Context {
        thread_context,
        errors,
        program,
        locals: &mut locals,
        emit_deps: &mut emit_deps,
        poly_param_usages: &mut poly_param_usages,
        ast: &mut ast,
        infer: &mut infer,
        runs: ExecutionTime::RuntimeFunc,
    };

    // Build the tree relationship between the different types.
    let root = ctx.ast.root;
    let root_value_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);
    build_constraints(&mut ctx, root, root_value_set);

    YieldData {
        ast,
        locals,
        emit_deps,
        infer,
        poly_param_usages,
    }
}

pub fn solve<'a>(
    errors: &mut ErrorCtx,
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    data: &mut YieldData,
) {
    let mut ctx = Context {
        thread_context,
        errors,
        program,
        locals: &mut data.locals,
        emit_deps: &mut data.emit_deps,
        poly_param_usages: &mut data.poly_param_usages,
        ast: &mut data.ast,
        infer: &mut data.infer,
        // This is only used in build_constraints, what it's set to doesn't matter
        runs: ExecutionTime::Never,
    };

    loop {
        ctx.infer.solve();

        let mut progress = false;
        for value_set_id in ctx.infer.value_sets.iter_ids() {
            let value_set = ctx.infer.value_sets.get_mut(value_set_id);
            if value_set_id == 0 // <- We don't want the base node, it's a special case, since it can't be dealt with by emit_execution_context; it can be any node.
            || value_set.has_errors
            || value_set.has_been_computed
            || value_set.uncomputed_values() > 0
            {
                continue;
            }

            debug_assert_eq!(value_set.uncomputed_values(), 0, "The number of uncomputed values cannot be less than zero");

            let related_nodes = std::mem::take(&mut value_set.related_nodes);
            for &node_id in &related_nodes {
                let node = ctx.ast.get_mut(node_id);
                if node.type_.is_none() {
                    node.type_ = Some(ctx.infer.value_to_compiler_type(node.type_infer_value_id));
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

            subset_was_completed(&mut ctx, waiting_on, value_set_id);

            progress = true;
        }

        if !progress {
            break;
        }
    }
}

pub fn finish<'a>(
    errors: &mut ErrorCtx,
    mut from: YieldData,
) -> Result<Result<(DependencyList, LocalVariables, TypeSystem, Ast), (DependencyList, YieldData)>, ()> {
    debug_assert!(from.poly_param_usages.is_empty(), "Cannot finish something that still has poly params");

    let mut are_incomplete_sets = false;
    for value_set_id in from.infer.value_sets.iter_ids() {
        let value_set = from.infer.value_sets.get(value_set_id);
        if value_set.has_errors || value_set.uncomputed_values() > 0 {
            errors.global_error(format!("Set {} is uncomputable! (uncomputability doesn't have a proper error yet, this is temporary)", value_set_id));
            are_incomplete_sets = true;
        }
    }

    if are_incomplete_sets | from.infer.output_errors(errors, &from.ast, &from.locals) {
        from.infer.output_incompleteness_errors(errors, &from.ast, &from.locals);
        from.infer.flag_all_values_as_complete();
        return Err(());
    }

    // @Temporary: Just to make it work for now, we should really only deal with the base set
    for node in &mut from.ast.nodes {
        if node.type_.is_none() {
            node.type_ = Some(from.infer.value_to_compiler_type(node.type_infer_value_id));
        }
    }

    for local in from.locals.iter_mut() {
        if local.type_.is_none() {
            local.type_ = Some(from.infer.value_to_compiler_type(local.type_infer_value_id));
        }
    }

    Ok(Ok((from.emit_deps, from.locals, from.infer, from.ast)))
}

fn subset_was_completed(ctx: &mut Context<'_, '_>, waiting_on: WaitingOnTypeInferrence, set: ValueSetId) {
    match waiting_on {
        WaitingOnTypeInferrence::MonomorphiseMember { node_id, poly_member_id, when_needed, params, parent_set } => {
            let mut fixed_up_params = Vec::with_capacity(params.len());
            for param in params {
                fixed_up_params.push(ctx.infer.extract_constant(param));
            }

            let wanted_dep = match when_needed {
                ExecutionTime::Typing => MemberDep::ValueAndCallableIfFunction,
                _ => MemberDep::Type,
            };

            if let Ok(member_id) = ctx.program.monomorphise_poly_member(ctx.errors, ctx.thread_context, poly_member_id, &fixed_up_params, wanted_dep) {
                let (type_, meta_data) = ctx.program.get_member_meta_data(member_id);
                let compiler_type = ctx.infer.add_compiler_type(type_, parent_set);
                ctx.infer.set_equal(ctx.ast.get(node_id).type_infer_value_id, compiler_type, Variance::Invariant);
                ctx.ast.get_mut(node_id).kind = NodeKind::ResolvedGlobal(member_id, meta_data.clone());
                ctx.infer.value_sets.unlock(parent_set);
            }
        }
        WaitingOnTypeInferrence::ValueIdFromConstantComputation { computation, value_id } => {
            let len_loc = ctx.ast.get(computation).loc;
            match crate::interp::emit_and_run(
                ctx.thread_context,
                ctx.program,
                ctx.locals,
                ctx.infer,
                ctx.ast,
                computation,
                set,
                &mut vec![len_loc],
            ) {
                Ok(constant_ref) => {
                    let type_id = ctx.ast.get(computation).type_infer_value_id;
                    let finished_value = ctx.infer.add_value(type_id, constant_ref, set);
                    
                    ctx.infer.set_equal(finished_value, value_id, Variance::Invariant);
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
        WaitingOnTypeInferrence::FunctionDeclarationInTyping {
            node_id,
            body,
            function_type,
            parent_set,
            emit_deps,
            function_id,
            time,
        } => {
            let type_ = ctx.infer.value_to_compiler_type(function_type);

            match time {
                ExecutionTime::Never => return,
                ExecutionTime::RuntimeFunc | ExecutionTime::Emission => {
                    ctx.program.queue_task(
                        emit_deps,
                        Task::EmitFunction(
                            ctx.locals.clone(),
                            ctx.infer.clone(),
                            ctx.ast.clone(),
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
                        ctx.ast,
                        body,
                        type_,
                        function_id,
                        set,
                    );
                }
            }

            let function_id_buffer = ctx
                .program
                .insert_buffer(type_, &function_id as *const _ as *const u8);

            // @Improvement: We could technically emit this constant
            // node _before_ queueing/emitting the function. It doesn't
            // really have a point though and makes things more complicated
            // when you start thinking about the typing-time functions.
            ctx.ast.get_mut(node_id).kind = NodeKind::Constant(
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
            let node = ctx.ast.get_mut(node_id);
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
                    &mut ctx.thread_context.c_declarations,
                    &routine,
                    args,
                    *returns,
                );
                ctx.thread_context.c_declarations.push_str("}\n");
            }

            ctx.ast.get_mut(node_id).kind = NodeKind::Constant(
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
    node_id: NodeId,
    set: ValueSetId,
) -> type_infer::ValueId {
    let node = ctx.ast.get(node_id);
    let node_loc = node.loc;
    let node_type_id = node.type_infer_value_id;

    ctx.infer.set_value_set(node_type_id, set);
    ctx.infer.value_sets.add_node_to_set(set, node_id);

    match node.kind {
        NodeKind::Uninit | NodeKind::Zeroed | NodeKind::ImplicitType => {}
        NodeKind::PolymorphicArgument(index) => {
            ctx.infer.value_sets.lock(set);
            ctx.infer.set_type(node_type_id, TypeKind::Polymorph(index), (), set);
            ctx.poly_param_usages.push((index, node_type_id, node_id, set));
        }
        NodeKind::Cast { value } => {
            let result_value = build_constraints(ctx, value, set);
            ctx.infer.set_cast(node_type_id, result_value);
        }
        NodeKind::BitCast { value } => {
            build_constraints(ctx, value, set);
        }
        NodeKind::Empty => {
            // @Performance: We could set the type directly(because no inferrence has happened yet),
            // this is a roundabout way of doing things.
            let temp = ctx.infer.add_type(type_infer::TypeKind::Empty, [], set);
            ctx.infer.set_equal(node_type_id, temp, Variance::Invariant);
        }
        // @Cleanup: We could unify these two nodes probably
        NodeKind::Global(scope, name, ref poly_params) | NodeKind::GlobalForTyping(scope, name, ref poly_params) => {
            let id = ctx.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");

            match id {
                PolyOrMember::Poly(id) => {
                    let num_args = ctx.program.get_num_poly_args(id);
                    if num_args != poly_params.len() {
                        ctx.errors.error(node_loc, "Passed polymorphic parameters even though this value isn't polymorphic".to_string());
                        // @Cleanup: This should probably just be a function on TypeSystem
                        ctx.infer.value_sets.get_mut(set).has_errors |= true;
                        return node_type_id;
                    }

                    let params = poly_params.clone();
                    let sub_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);
                    let mut param_values = Vec::with_capacity(params.len());
                    for &param in &params {
                        let (_, param_value_id) = build_inferrable_constant_value(ctx, param, sub_set);
                        param_values.push(param_value_id);
                    }
                    
                    ctx.infer.value_sets.lock(set);

                    ctx.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::MonomorphiseMember {
                        node_id,
                        poly_member_id: id,
                        when_needed: ctx.runs,
                        params: param_values,
                        parent_set: set,
                    });
                }
                PolyOrMember::Member(id) => {
                    if !poly_params.is_empty() {
                        // This is an error, since it's not polymorphic
                        ctx.errors.error(node_loc, "Passed polymorphic parameters even though this value isn't polymorphic".to_string());
                        // @Cleanup: This should probably just be a function on TypeSystem
                        ctx.infer.value_sets.get_mut(set).has_errors |= true;
                        return node_type_id;
                    }

                    let (type_, meta_data) = ctx.program.get_member_meta_data(id);

                    let type_id = ctx.infer.add_compiler_type(
                        type_,
                        set,
                    );

                    ctx.infer.set_equal(node_type_id, type_id, Variance::Invariant);

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

                    ctx.ast.get_mut(node_id).kind = NodeKind::ResolvedGlobal(id, meta_data);
                }
            }
        }
        NodeKind::While {
            condition,
            iteration_var,
            body,
            else_body,
            label,
        } => {
            ctx.locals.get_mut(iteration_var).stack_frame_id = set;
            ctx.locals.get_label_mut(label).stack_frame_id = set;

            ctx.infer.set_int(ctx.locals.get(iteration_var).type_infer_value_id, IntTypeKind::Usize, set);

            let condition_type_id = build_constraints(ctx, condition, set);
            let bool_type = ctx.infer.add_type(TypeKind::Bool, [], set);
            ctx.infer.set_equal(condition_type_id, bool_type, Variance::Invariant);

            let label_type_infer_id = ctx.locals.get_label(label).type_infer_value_id;

            build_constraints(ctx, body, set);

            match else_body {
                Some(else_body) => {
                    let else_type = build_constraints(ctx, else_body, set);
                    ctx.infer.set_equal(label_type_infer_id, else_type, Variance::Invariant);
                }
                None => {
                    let empty_type = ctx.infer.add_type(TypeKind::Empty, [], set);
                    ctx.infer.set_equal(label_type_infer_id, empty_type, Variance::Invariant);
                }
            }

            ctx.infer.set_equal(node_type_id, label_type_infer_id, Variance::Invariant);
        }
        NodeKind::For {
            iterator,
            iteration_var,
            iterating,
            body,
            else_body,
            label,
        } => {
            ctx.locals.get_mut(iteration_var).stack_frame_id = set;
            ctx.locals.get_mut(iterator).stack_frame_id = set;
            ctx.locals.get_label_mut(label).stack_frame_id = set;

            ctx.infer.set_int(ctx.locals.get(iteration_var).type_infer_value_id, IntTypeKind::Usize, set);

            // The type the body returns doesn't matter, since we don't forward it.
            let iterating_type_id = build_constraints(ctx, iterating, set);

            build_constraints(ctx, body, set);

            let label_type_infer_id = ctx.locals.get_label(label).type_infer_value_id;

            ctx.infer.set_field_name_equal(iterating_type_id, "ptr".into(), ctx.locals.get(iterator).type_infer_value_id, Variance::Invariant);

            match else_body {
                Some(else_body) => {
                    let else_type = build_constraints(ctx, else_body, set);
                    ctx.infer.set_equal(label_type_infer_id, else_type, Variance::Invariant);
                }
                None => {
                    let empty_type = ctx.infer.add_type(TypeKind::Empty, [], set);
                    ctx.infer.set_equal(label_type_infer_id, empty_type, Variance::Invariant);
                }
            }

            ctx.infer.set_equal(node_type_id, label_type_infer_id, Variance::Invariant);
        }
        NodeKind::Literal(Literal::Int(_)) => {
            ctx.infer.set_type(node_type_id, TypeKind::Int, (), set);
        }
        NodeKind::Defer { deferring } => {
            build_constraints(ctx, deferring, set);
            let empty_id = ctx.infer.add_type(
                TypeKind::Empty, [],
                set,
            );

            ctx.infer.set_equal(node_type_id, empty_id, Variance::Invariant);
        }
        NodeKind::Literal(Literal::String(ref data)) => {
            let u8_type = ctx.infer.add_int(IntTypeKind::U8, set);
            ctx.infer.set_type(node_type_id, TypeKind::Buffer, [u8_type], set);

            let u8_type = types::Type::new(types::TypeKind::Int(IntTypeKind::U8));
            let type_ = types::Type::new(types::TypeKind::Buffer { permits: PtrPermits::READ, pointee: u8_type });
            let ptr = ctx.program.insert_buffer(
                type_,
                &crate::types::BufferRepr {
                    ptr: data.as_ptr() as *mut _,
                    length: data.len(),
                } as *const _ as *const _,
            );
            ctx.ast.get_mut(node_id).kind = NodeKind::Constant(ptr, None);
        }
        NodeKind::BuiltinFunction(function) => {
            let function_type_id = ctx.infer.add_unknown_type();
            let sub_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::BuiltinFunctionInTyping {
                node_id,
                function,
                type_: function_type_id,
                parent_set: set,
            });

            // The parent value set has to wait for this function declaration to be emitted until
            // it can continue, so we lock it to make sure it doesn't get emitted before then.
            ctx.infer.value_sets.lock(set);

            ctx.infer.set_type(function_type_id, TypeKind::Function, (), sub_set);
            ctx.infer.set_equal(node_type_id, function_type_id, Variance::Invariant);
        }
        NodeKind::ArrayLiteral(ref args) => {
            let inner_type = ctx.infer.add_unknown_type_with_set(set);

            let args = args.clone();
            for &arg in &args {
                let arg_type_id = build_constraints(ctx, arg, set);
                ctx.infer.set_equal(arg_type_id, inner_type, Variance::Variant);
            }

            let usize = ctx.infer.add_int(IntTypeKind::Usize, set);
            let length = ctx.program.insert_buffer(types::Type::new(types::TypeKind::Int(IntTypeKind::Usize)), args.len().to_le_bytes().as_ptr());

            let variable_count = ctx.infer.add_value(
                usize,
                length,
                set,
            );

            let array_type = ctx.infer.add_type(
                TypeKind::Array, [inner_type, variable_count],
                set,
            );

            ctx.infer.set_equal(node_type_id, array_type, Variance::Invariant);
        }
        NodeKind::Member { of, name } => {
            let of_type_id = build_constraints(ctx, of, set);
            ctx.infer
                .set_field_name_equal(of_type_id, name, node_type_id, Variance::Invariant);
        }
        NodeKind::TypeOf(inner) => {
            let old = ctx.runs;
            ctx.runs = ctx.runs.combine(ExecutionTime::Never);
            let type_ = build_constraints(ctx, inner, set);
            ctx.runs = old;
            ctx.infer.set_equal(node_type_id, type_, Variance::Invariant);
        }
        NodeKind::Local(local_id) => {
            let local = ctx.locals.get(local_id);
            let local_type_id = local.type_infer_value_id;
            ctx.infer
                .set_equal(local_type_id, node_type_id, Variance::Invariant);

            if ctx.runs != ExecutionTime::Never && local.stack_frame_id != set {
                dbg!(local.stack_frame_id);
                ctx.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type". to_string());
                ctx.infer.value_sets.get_mut(set).has_errors = true;
            }
        }
        NodeKind::If {
            condition,
            true_body,
            false_body,
        } => {
            let condition_type_id = build_constraints(ctx, condition, set);
            // @Performance: This could be better, I really want a constraint for this kind of thing...
            let condition_type = ctx.infer.add_type(TypeKind::Bool, [], set);
            ctx.infer
                .set_equal(condition_type_id, condition_type, Variance::Invariant);

            let true_body_id = build_constraints(ctx, true_body, set);
            let false_body_id = match false_body {
                Some(id) => build_constraints(ctx, id, set),
                None => ctx.infer.add_type(
                    TypeKind::Empty, [],
                    set,
                ),
            };

            ctx.infer
                .set_equal(true_body_id, node_type_id, Variance::Variant);
            ctx.infer
                .set_equal(false_body_id, node_type_id, Variance::Variant);
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
            operand,
        } => {
            let operand_type_id = build_constraints(ctx, operand, set);

            let temp = ctx.infer.add_type(
                TypeKind::Reference,
                [node_type_id],
                set,
            );
            ctx.infer
                .set_equal(operand_type_id, temp, Variance::Invariant);
        }
        NodeKind::ArrayType { len, members } => {
            let (length_type, length_value) = build_inferrable_constant_value(ctx, len, set);
            let usize_type = ctx.infer.add_int(IntTypeKind::Usize, set);
            ctx.infer.set_equal(usize_type, length_type, Variance::Invariant);

            let member_type_id = build_constraints(ctx, members, set);
            ctx.infer.set_type(node_type_id, TypeKind::Array, [member_type_id, length_value], set);
        }
        NodeKind::FunctionDeclaration {
            ref args,
            returns,
            body,
        } => {
            // @Speed: Somewhat needless allocation
            let args = args.to_vec();

            let mut emit_deps = DependencyList::new();

            let mut sub_ctx = Context {
                thread_context: ctx.thread_context,
                errors: ctx.errors,
                program: ctx.program,
                locals: ctx.locals,
                emit_deps: &mut emit_deps,
                poly_param_usages: ctx.poly_param_usages,
                ast: ctx.ast,
                infer: ctx.infer,
                runs: ctx.runs.combine(ExecutionTime::RuntimeFunc),
            };

            let sub_set = sub_ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);

            // The parent value set has to wait for this function declaration to be emitted until
            // it can continue, so we lock it to make sure it doesn't get emitted before then.
            sub_ctx.infer.value_sets.lock(set);

            let mut function_type_ids = Vec::with_capacity(args.len() + 1);
            let returns_type_id = build_constraints(&mut sub_ctx, returns, sub_set);
            function_type_ids.push(returns_type_id);

            for (local_id, type_node) in args {
                let local = sub_ctx.locals.get_mut(local_id);
                local.stack_frame_id = sub_set;
                let local_type_id = local.type_infer_value_id;
                let type_id = build_constraints(&mut sub_ctx, type_node, sub_set);
                sub_ctx.infer.set_value_set(local_type_id, sub_set);
                sub_ctx.infer
                    .set_equal(type_id, local_type_id, Variance::Invariant);
                function_type_ids.push(type_id);
            }

            let body_type_id = build_constraints(&mut sub_ctx, body, sub_set);

            ctx.infer
                .set_equal(body_type_id, returns_type_id, Variance::Variant);

            let infer_type_id = ctx.infer.add_type(TypeKind::Function, function_type_ids.into_boxed_slice(), sub_set);
            ctx.infer
                .set_equal(infer_type_id, node_type_id, Variance::Invariant);

            let function_id = ctx.program.insert_function(node_loc);
            ctx.emit_deps.add(node_loc, DepKind::Callable(function_id));

            ctx.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::FunctionDeclarationInTyping {
                node_id,
                body,
                function_type: infer_type_id,
                parent_set: set,
                emit_deps,
                function_id,
                time: ctx.runs,
            });
        }
        NodeKind::FunctionCall { calling, ref args } => {
            // @Speed: Somewhat needless allocation
            let args = args.to_vec();

            let calling_type_id = build_constraints(ctx, calling, set);

            // A little bit hacky, but since we are invariant to the return type
            // (variance is always applied before merges of types essentially, and this is the creation of a type),
            // we can get away with this.
            let return_type = node_type_id;

            let mut typer_args = Vec::with_capacity(args.len() + 1);
            typer_args.push(return_type);

            for &arg in &args {
                let function_arg_type_id = ctx.infer.add_unknown_type();
                let arg_type_id = build_constraints(ctx, arg, set);
                ctx.infer.set_equal(function_arg_type_id, arg_type_id, Variance::Covariant);
                typer_args.push(function_arg_type_id);
            }

            // Specify that the caller has to be a function type
            let type_id = ctx.infer.add_type(TypeKind::Function, typer_args.into_boxed_slice(), set);
            ctx.infer
                .set_equal(calling_type_id, type_id, Variance::Invariant);

            ctx.ast.get_mut(node_id).kind = NodeKind::ResolvedFunctionCall {
                calling,
                args: args.into_iter().enumerate().collect(),
            };
        }
        NodeKind::Declare {
            local,
            dummy_local_node: left,
            value: right,
        } => {
            // Set the set of the local to this type set
            let local = ctx.locals.get_mut(local);
            local.stack_frame_id = set;
            ctx.infer.set_value_set(local.type_infer_value_id, set);

            // let access = ctx.infer.add_access(
            //     Some(Access::needs(false, true)),
            //     set,
            // );
            let left_type_id = build_lvalue(ctx, left, set);
            let right_type_id = build_constraints(ctx, right, set);

            ctx.infer
                .set_equal(left_type_id, right_type_id, Variance::Covariant);

            ctx.infer.set_type(
                node_type_id,
                TypeKind::Empty, [],
                set,
            );
        }
        NodeKind::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        } => {
            let left_type_id = build_lvalue(ctx, left, set);
            let right_type_id = build_constraints(ctx, right, set);

            ctx.infer
                .set_equal(left_type_id, right_type_id, Variance::Covariant);

            ctx.infer.set_type(
                node_type_id,
                TypeKind::Empty, [],
                set,
            );
        }
        NodeKind::Binary { op, left, right } => {
            let left = build_constraints(ctx, left, set);
            let right = build_constraints(ctx, right, set);
            ctx.infer.set_op_equal(op, left, right, node_type_id);
        }
        NodeKind::Reference(operand) => {
            let inner = build_lvalue(ctx, operand, set);
            ctx.infer.set_type(
                node_type_id,
                TypeKind::Reference,
                [inner],
                set,
            );
        }
        NodeKind::Block {
            ref contents,
            label,
        } => {
            if let Some(label) = label {
                let label = ctx.locals.get_label_mut(label);
                ctx.infer.set_equal(label.type_infer_value_id, node_type_id, Variance::Invariant);
                label.stack_frame_id = set;
            }

            let last = *contents.last().unwrap();
            // @Performance: This isn't very fast, but it's fine for now
            for statement_id in contents[..contents.len() - 1].to_vec() {
                build_constraints(ctx, statement_id, set);
            }

            let last_type_id = build_constraints(ctx, last, set);
            ctx.infer
                .set_equal(node_type_id, last_type_id, Variance::Invariant);
        }
        NodeKind::Break {
            label,
            num_defer_deduplications: _,
            value,
        } => {
            let label = ctx.locals.get_label(label);
            if ctx.runs != ExecutionTime::Never && label.stack_frame_id != set {
                ctx.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type".to_string());
                ctx.infer.value_sets.get_mut(set).has_errors = true;
            }

            let label_type_id = label.type_infer_value_id;

            let value_type_id = build_constraints(ctx, value, set);
            ctx.infer.set_equal(value_type_id, label_type_id, Variance::Variant);

            ctx.infer.set_type(
                node_type_id,
                TypeKind::Empty, [],
                set,
            );
        }
        NodeKind::Parenthesis(inner) => {
            let inner_type_id = build_constraints(ctx, inner, set);
            ctx.infer
                .set_equal(inner_type_id, node_type_id, Variance::Invariant);
        }
        NodeKind::TypeBound { value, bound } => {
            let bound_type_id = build_constraints(ctx, bound, set);
            ctx.infer
                .set_equal(node_type_id, bound_type_id, Variance::Invariant);
            let value_type_id = build_constraints(ctx, value, set);
            ctx.infer
                .set_equal(value_type_id, node_type_id, Variance::Variant);
        }
        NodeKind::LiteralType(type_) => {
            ctx.infer.set_compiler_type(node_type_id, type_, set);
            // ctx.infer.set_equal(node_type_id, compiler_type, Variance::Invariant);
        }
        NodeKind::FunctionType { ref args, returns } => {
            // @Speed: Somewhat needless allocation
            let args = args.to_vec();

            let mut function_type_ids = Vec::with_capacity(args.len() + 1);
            let returns_type_id = build_constraints(ctx, returns, set);
            function_type_ids.push(returns_type_id);

            for type_node in args {
                let type_id = build_constraints(ctx, type_node, set);
                function_type_ids.push(type_id);
            }

            let infer_type_id = ctx.infer.add_type(TypeKind::Function, function_type_ids.into_boxed_slice(), set);
            ctx.infer
                .set_equal(infer_type_id, node_type_id, Variance::Invariant);
        }
        NodeKind::StructType { ref fields } => {
            // @Performance: Many allocations
            let names = fields.iter().map(|v| v.0).collect();
            let fields = fields.iter().map(|v| v.1).collect::<Vec<_>>();
            let fields: Box<_> = fields
                .into_iter()
                .map(|v| build_constraints(ctx, v, set))
                .collect();
            ctx.infer.set_type(node_type_id, TypeKind::Struct(names), fields, set);
        }
        NodeKind::ReferenceType(inner, _permits) => {
            let inner = build_constraints(ctx, inner, set);
            // let access = permits_to_access(permits);
            // let access = ctx.infer.add_access(Some(access), set);
            ctx.infer.set_type(
                node_type_id,
                TypeKind::Reference, [inner],
                set,
            );
        }
        NodeKind::BufferType(inner, _permits) => {
            let inner = build_constraints(ctx, inner, set);
            // let access = permits_to_access(permits);
            // let access = ctx.infer.add_access(Some(access), set);
            ctx.infer.set_type(
                node_type_id,
                TypeKind::Buffer, [inner],
                set,
            );
        }
        _ => unimplemented!(
            "Ast node does not have a typing relationship yet {:?}",
            node.kind
        ),
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
    node_id: NodeId,
    // access: type_infer::ValueId,
    set: ValueSetId,
) -> type_infer::ValueId {
    let node = ctx.ast.get(node_id);
    let node_loc = node.loc;
    let node_type_id = node.type_infer_value_id;

    match node.kind {
        NodeKind::Member { of, name } => {
            let of_type_id = build_lvalue(ctx, of, set);
            ctx.infer
                .set_field_name_equal(of_type_id, name, node_type_id, Variance::Invariant);
        }
        NodeKind::Local(local_id) => {
            let local = ctx.locals.get(local_id);
            let local_type_id = local.type_infer_value_id;
            ctx.infer
                .set_equal(local_type_id, node_type_id, Variance::Invariant);

            if local.stack_frame_id != set {
                ctx.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type".to_string());
                ctx.infer.value_sets.get_mut(set).has_errors = true;
            }
        }
        NodeKind::Parenthesis(value) => {
            let inner = build_lvalue(ctx, value, set);
            ctx.infer.set_equal(node_type_id, inner, Variance::Invariant);
        }
        NodeKind::TypeBound { value, bound } => {
            // @Improvment: Here, both things are invariant. One of them could potentially be variant,
            // but only in some cases. After I think about how cases like this actually work,
            // I could try integrating this variance with the `access` variance passed in here to make it
            // less restrictive. It would also be nice if it was consistant with how non lvalue typebounds work,
            // since right now that's an inconsistancy that's going to be weird if you trigger it.
            let bound_type_id = build_constraints(ctx, bound, set);
            ctx.infer
                .set_equal(node_type_id, bound_type_id, Variance::Invariant);
            let value_type_id = build_lvalue(ctx, value, set);
            ctx.infer
                .set_equal(value_type_id, node_type_id, Variance::Invariant);
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
            operand,
        } => {
            let temp = ctx.infer.add_type(
                TypeKind::Reference,
                [node_type_id],
                set,
            );

            let operand_type_id = build_constraints(ctx, operand, set);
            ctx.infer
                .set_equal(operand_type_id, temp, Variance::Invariant);
        }
        _ => {
            // Make it a reference to a temporary instead. This forces the pointer to be readonly.
            // TODO: Make it require it to be read-only here.
            return build_constraints(ctx, node_id, set);
        }
    }

    ctx.infer.set_value_set(node_type_id, set);
    ctx.infer.value_sets.add_node_to_set(set, node_id);

    node_type_id
}

// The first return is the type of the constant, the second return is the value id of that constant, where the constant will later be stored.
fn build_inferrable_constant_value(
    ctx: &mut Context<'_, '_>,
    node_id: NodeId,
    set: ValueSetId,
) -> (type_infer::ValueId, type_infer::ValueId) {
    let node = ctx.ast.get(node_id);
    let _node_loc = node.loc;
    let node_type_id = node.type_infer_value_id;

    let value_id = match node.kind {
        _ => {
            // We can't figure it out in a clever way, so just compile time execute the node as a constant.
            let mut sub_ctx = Context {
                thread_context: ctx.thread_context,
                errors: ctx.errors,
                program: ctx.program,
                locals: ctx.locals,
                emit_deps: ctx.emit_deps,
                poly_param_usages: ctx.poly_param_usages,
                ast: ctx.ast,
                infer: ctx.infer,
                runs: ctx.runs.combine(ExecutionTime::Typing),
            };
            let sub_set = sub_ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);

            let constant_type_id = build_constraints(&mut sub_ctx, node_id, sub_set);
            let value_id = ctx.infer.add_value(constant_type_id, (), set);
            ctx.infer.set_equal(node_type_id, constant_type_id, Variance::Invariant);

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

#[derive(Clone)]
pub enum WaitingOnTypeInferrence {
    MonomorphiseMember {
        node_id: NodeId,
        poly_member_id: PolyMemberId,
        when_needed: ExecutionTime,
        params: Vec<type_infer::ValueId>,
        parent_set: ValueSetId,
    },
    FunctionDeclarationInTyping {
        node_id: NodeId,
        body: NodeId,
        function_type: TypeId,
        /// This is because function declaration create a constant in the
        /// parent set, and we have to make sure that the parent set isn't
        /// emitted before that constant is created.
        parent_set: ValueSetId,
        emit_deps: DependencyList,
        function_id: FunctionId,
        time: ExecutionTime,
    },
    BuiltinFunctionInTyping {
        node_id: NodeId,
        function: BuiltinFunction,
        type_: TypeId,
        parent_set: ValueSetId,
    },
    ValueIdFromConstantComputation {
        computation: NodeId,
        value_id: type_infer::ValueId,
    },
    None,
}
