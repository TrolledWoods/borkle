use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::execution_time::ExecutionTime;
use crate::locals::{LocalId, LocalVariables};
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
pub use crate::parser::{ast::Node, ast::NodeId, ast::NodeKind, Ast};
use crate::program::constant::ConstantRef;
use crate::program::{MemberMetaData, PolyOrMember, Program, Task};
use crate::thread_pool::ThreadContext;
use crate::type_infer::{self, Access, Reason, TypeSystem, ValueSetId, Variance, Type, TypeKind};
use crate::types::{self, IntTypeKind, PtrPermits};
use std::sync::Arc;
use std::mem;

pub struct YieldData {
    emit_deps: DependencyList,
    locals: LocalVariables,
    ast: Ast,
}

impl YieldData {
    pub fn new(locals: LocalVariables, ast: Ast) -> Self {
        Self {
            emit_deps: DependencyList::new(),
            ast,
            locals,
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
    runs: ExecutionTime,
}

pub fn process_ast<'a>(
    errors: &mut ErrorCtx,
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    from: YieldData,
) -> Result<Result<(DependencyList, LocalVariables, Ast), (DependencyList, YieldData)>, ()> {
    profile::profile!("Type ast");

    let mut ast = from.ast;
    let mut locals = from.locals;
    let mut infer = TypeSystem::new(program);

    // Create type inference variables for all variables and nodes, so that there's a way to talk about
    // all of them.
    for node in &mut ast.nodes {
        node.type_infer_value_id = infer.add_unknown_type();
    }

    for local in locals.iter_mut() {
        local.type_infer_value_id = infer.add_unknown_type();
    }

    let mut emit_deps = from.emit_deps;

    let mut ctx = Context {
        thread_context,
        errors,
        program,
        locals: &mut locals,
        emit_deps: &mut emit_deps,
        ast: &mut ast,
        infer: &mut infer,
        runs: ExecutionTime::RuntimeFunc,
    };

    // Build the tree relationship between the different types.
    let root = ctx.ast.root;
    let root_value_set = ctx.infer.value_sets.add(root);
    build_constraints(&mut ctx, root, root_value_set);

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
            let node_id = value_set.ast_node;

            emit_execution_context(&mut ctx, node_id, value_set_id);

            progress = true;
        }

        if !progress {
            break;
        }
    }

    // println!("\nLocals:\n");
    // for local in ctx.locals.iter() {
    //     println!(
    //         "{}: {}",
    //         local.name,
    //         ctx.infer.value_to_str(local.type_infer_value_id, 0)
    //     );
    // }

    if ctx.infer.output_errors(ctx.errors) {
        ctx.infer.flag_all_values_as_complete();
        return Err(());
    }

    let mut are_incomplete_sets = false;
    for value_set_id in ctx.infer.value_sets.iter_ids() {
        let value_set = ctx.infer.value_sets.get(value_set_id);
        if value_set.has_errors || value_set.uncomputed_values() > 0 {
            ctx.errors.global_error(format!("Set {} is uncomputable! (uncomputability doesn't have a proper error yet, this is temporary)", value_set_id));
            are_incomplete_sets = true;
        }
    }

    if are_incomplete_sets {
        ctx.infer.flag_all_values_as_complete();
        return Err(());
    }

    // @Temporary: Just to make it work for now, we should really only deal with the base set
    for node in &mut ctx.ast.nodes {
        if node.type_.is_none() {
            node.type_ = Some(ctx.infer.value_to_compiler_type(node.type_infer_value_id));
        }
    }

    for local in ctx.locals.iter_mut() {
        if local.type_.is_none() {
            local.type_ = Some(ctx.infer.value_to_compiler_type(local.type_infer_value_id));
        }
    }

    Ok(Ok((emit_deps, locals, ast)))
}

fn emit_execution_context(ctx: &mut Context<'_, '_>, node_id: NodeId, set: ValueSetId) {
    let node = ctx.ast.get_mut(node_id);
    let node_type_id = node.type_infer_value_id;
    let node_loc = node.loc;

    // @Hack: We replace the kind with a temporary, since all the nodes here are only for this function,
    // and have to replaced for emission anyway.
    let kind = std::mem::replace(&mut node.kind, NodeKind::Empty);
    match kind {
        NodeKind::ArrayTypeInTyping { len, length_value } => {
            match crate::interp::emit_and_run(
                ctx.thread_context,
                ctx.program,
                &mut ctx.locals,
                &ctx.ast,
                len,
                set,
                &mut vec![node_loc],
            ) {
                Ok(constant_ref) => {
                    // @Hack: We get the usize from the variable so we don't have to add a reason for it
                    let usize = ctx.ast.get(len).type_infer_value_id;
                    let variable_count = ctx.infer.add(
                        type_infer::ValueKind::Value(Some(type_infer::Constant {
                            type_: usize,
                            value: Some(constant_ref),
                        })),
                        // This value is already complete, so the set doesn't matter
                        set,
                        Reason::new(ctx.ast.get(len).loc, "the number of elements specified here"),
                    );
                    
                    ctx.infer.set_equal(variable_count, length_value, Variance::Invariant);
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
        NodeKind::FunctionDeclarationInTyping {
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
                        &mut ctx.locals,
                        &ctx.ast,
                        body,
                        type_,
                        function_id,
                        set,
                    );
                }
            }
            // }

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
        NodeKind::BuiltinFunctionInTyping {
            function,
            type_,
            parent_set,
        } => {
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
        _ => unreachable!("A {:?} doesn't define an execution context", node.kind),
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
        NodeKind::Empty => {
            // @Performance: We could set the type directly(because no inferrence has happened yet),
            // this is a roundabout way of doing things.
            let temp = ctx.infer.add_t(type_infer::TypeKind::Empty, [], set, Reason::new(node_loc, "this value is empty"));
            ctx.infer.set_equal(node_type_id, temp, Variance::Invariant);
        }
        // @Cleanup: We could unify these two nodes probably
        NodeKind::Global(scope, name, ref poly_params) | NodeKind::GlobalForTyping(scope, name, ref poly_params) => {
            assert_eq!(poly_params.len(), 0, "polymorphic things not supported yet");

            let id = ctx.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");

            let PolyOrMember::Member(id) = id else { todo!("Polymorphism!") };

            let (type_, meta_data) = ctx.program.get_member_meta_data(id);

            let type_id = ctx.infer.add_compiler_type(
                type_,
                set,
                Reason::new(node_loc, format!("this global is '{}'", type_)),
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
        NodeKind::Literal(Literal::Int(_)) => {
            // TODO: Actually add a constraint that checks that the type is an int, and that it's in bounds
        }
        NodeKind::Defer { deferring } => {
            build_constraints(ctx, deferring, set);
            let empty_id = ctx.infer.add_t(
                TypeKind::Empty, [],
                set,
                Reason::new(
                    node_loc,
                    "this if evaluates to Empty because it doesn't have an else clause",
                ),
            );

            ctx.infer.set_equal(node_type_id, empty_id, Variance::Invariant);
        }
        NodeKind::Literal(Literal::String(ref data)) => {
            let reason = Reason::new(node_loc, "of this string literal");
            let access = ctx.infer.add_access(
                Some(type_infer::Access::disallows(None, Some(Reason::new(node_loc, "string literals cannot be written to")))),
                set,
                reason.clone(),
            );
            let u8_type = ctx.infer.add_int(IntTypeKind::U8, set, reason.clone());
            ctx.infer.set_type(node_type_id, TypeKind::Buffer, [access, u8_type], set, reason.clone());

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
            let sub_set = ctx.infer.value_sets.add(node_id);

            // The parent value set has to wait for this function declaration to be emitted until
            // it can continue, so we lock it to make sure it doesn't get emitted before then.
            ctx.infer.value_sets.lock(set);

            ctx.infer.set_type(node_type_id, TypeKind::Function, (), sub_set, Reason::new(node_loc, "this builtin function is a function (surprising!)"));

            ctx.ast.get_mut(node_id).kind = NodeKind::BuiltinFunctionInTyping {
                function,
                type_: node_type_id,
                parent_set: set,
            };
        }
        NodeKind::ArrayLiteral(ref args) => {
            let inner_type = ctx.infer.add_unknown_type_with_set(set);

            let args = args.clone();
            for &arg in &args {
                let arg_type_id = build_constraints(ctx, arg, set);
                ctx.infer.set_equal(arg_type_id, inner_type, Variance::Variant);
            }

            let usize = ctx.infer.add_int(IntTypeKind::Usize, set, Reason::new(node_loc, "array lengths are usize"));
            let length = ctx.program.insert_buffer(types::Type::new(types::TypeKind::Int(IntTypeKind::Usize)), args.len().to_le_bytes().as_ptr());

            let variable_count = ctx.infer.add_value(
                usize,
                length,
                set,
                Reason::new(node_loc, format!("this array has {} elements", args.len())),
            );

            let array_type = ctx.infer.add_t(
                TypeKind::Array, [inner_type, variable_count],
                set,
                Reason::new(node_loc, format!("of this array literal")),
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
            let condition_loc = ctx.ast.get(condition).loc;
            // @Performance: This could be better, I really want a constraint for this kind of thing...
            let condition_type = ctx.infer.add(
                type_infer::ValueKind::Type(Some(type_infer::Type {
                    kind: type_infer::TypeKind::Bool,
                    args: Some(Box::new([])),
                })),
                set,
                Reason::new(condition_loc, "this if condition has to be a boolean"),
            );
            ctx.infer
                .set_equal(condition_type_id, condition_type, Variance::Invariant);

            let true_body_id = build_constraints(ctx, true_body, set);
            let false_body_id = match false_body {
                Some(id) => build_constraints(ctx, id, set),
                None => ctx.infer.add_t(
                    TypeKind::Empty, [],
                    set,
                    Reason::new(
                        node_loc,
                        "this if evaluates to Empty because it doesn't have an else clause",
                    ),
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

            let access = ctx.infer.add_access(
                Some(Access::needs(Some(Reason::new(node_loc, "this dereference requires read access")), None)),
                set,
                Reason::new(node_loc, "Temporary reason for declare until I simplify it"),
            );
            let temp = ctx.infer.add_t(
                TypeKind::Reference,
                [access, node_type_id],
                set,
                Reason::new(node_loc, "it was dereferenced here"),
            );
            ctx.infer
                .set_equal(operand_type_id, temp, Variance::Invariant);
        }
        NodeKind::ArrayType { len, members } => {
            let mut sub_ctx = Context {
                thread_context: ctx.thread_context,
                errors: ctx.errors,
                program: ctx.program,
                locals: ctx.locals,
                emit_deps: ctx.emit_deps,
                ast: ctx.ast,
                infer: ctx.infer,
                runs: ctx.runs.combine(ExecutionTime::Typing),
            };
            let sub_set = sub_ctx.infer.value_sets.add(node_id);

            let len_type_id = build_constraints(&mut sub_ctx, len, sub_set);
            let member_type_id = build_constraints(ctx, members, set);

            let usize_type = ctx.infer.add_int(IntTypeKind::Usize, set, Reason::new(node_loc, "array lengths are usize"));

            ctx.infer.set_equal(usize_type, len_type_id, Variance::Invariant);

            // @Cleanup: Adding without reason is a little bit scary, should we just add unknown instead?
            // @Performance: We can add some checks to see if the length calculation is actually simple
            // We don't check that it's part of the same set, because this is
            // all to compute a type; if we figure out a valid set of types
            // for the main thing but not for the array length, that's fine,
            // even if we create an error later the types matched for a moment,
            // enough to emit code.
            let length_value = ctx.infer.add_without_reason(
                type_infer::ValueKind::Value(Some(type_infer::Constant {
                    type_: usize_type,
                    value: None,
                })),
                set,
            );

            let array_type = ctx.infer.add(
                type_infer::ValueKind::Type(Some(type_infer::Type {
                    kind: type_infer::TypeKind::Array,
                    args: Some(Box::new([member_type_id, length_value])),
                })),
                set,
                Reason::new(node_loc, format!("of this array type")),
            );

            ctx.ast.get_mut(node_id).kind = NodeKind::ArrayTypeInTyping {
                len,
                length_value,
            };

            ctx.infer.set_equal(node_type_id, array_type, Variance::Invariant);
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
                ast: ctx.ast,
                infer: ctx.infer,
                runs: ctx.runs.combine(ExecutionTime::RuntimeFunc),
            };

            let sub_set = sub_ctx.infer.value_sets.add(node_id);

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

            let infer_type = type_infer::ValueKind::Type(Some(type_infer::Type {
                kind: type_infer::TypeKind::Function,
                args: Some(function_type_ids.into_boxed_slice()),
            }));
            let infer_type_id = ctx.infer.add(
                infer_type,
                sub_set,
                Reason::new(node_loc, "it was declared as a function here"),
            );
            ctx.infer
                .set_equal(infer_type_id, node_type_id, Variance::Invariant);

            let function_id = ctx.program.insert_function(node_loc);
            ctx.emit_deps.add(node_loc, DepKind::Callable(function_id));

            ctx.ast.get_mut(node_id).kind = NodeKind::FunctionDeclarationInTyping {
                body,
                function_type: infer_type_id,
                parent_set: set,
                emit_deps,
                function_id,
                time: ctx.runs,
            };
        }
        NodeKind::FunctionCall { calling, ref args } => {
            // @Speed: Somewhat needless allocation
            let args = args.to_vec();

            let calling_loc = ctx.ast.get(calling).loc;
            let calling_type_id = build_constraints(ctx, calling, set);

            // A little bit hacky, but since we are invariant to the return type
            // (variance is always applied before merges of types essentially, and this is the creation of a type),
            // we can get away with this.
            let return_type = node_type_id;

            let mut typer_args = Vec::with_capacity(args.len() + 1);
            typer_args.push(return_type);

            for (i, &arg) in args.iter().enumerate() {
                let function_arg_type_id = ctx.infer.add_unknown_type();
                let arg_type_id = build_constraints(ctx, arg, set);
                ctx.infer.set_equal(function_arg_type_id, arg_type_id, Variance::Covariant);
                typer_args.push(function_arg_type_id);
            }

            // Specify that the caller has to be a function type
            let infer_type = type_infer::ValueKind::Type(Some(type_infer::Type {
                kind: type_infer::TypeKind::Function,
                args: Some(typer_args.into_boxed_slice()),
            }));
            let type_id = ctx.infer.add(
                infer_type,
                set,
                Reason::new(calling_loc, "it was called here"),
            );
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

            let access = ctx.infer.add_access(
                Some(Access::needs(None, Some(Reason::new(node_loc, "Temporary reason for declare until I simplify it")))),
                set,
                Reason::new(node_loc, "Temporary reason for declare until I simplify it"),
            );
            let left_type_id = build_lvalue(ctx, left, access, set);
            let right_type_id = build_constraints(ctx, right, set);

            ctx.infer
                .set_equal(left_type_id, right_type_id, Variance::Covariant);

            ctx.infer.set_type(
                node_type_id,
                TypeKind::Empty, [],
                set,
                Reason::new(node_loc, "declaration return empty, however this reason should never be noticable by a user"),
            );
        }
        NodeKind::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        } => {
            let access = ctx.infer.add_access(
                Some(Access::needs(None, Some(Reason::new(node_loc, "it is assigned to here")))),
                set,
                Reason::new(
                    node_loc,
                    "assigned here, therefore needs to be a writable value",
                ),
            );
            let left_type_id = build_lvalue(ctx, left, access, set);
            let right_type_id = build_constraints(ctx, right, set);

            ctx.infer
                .set_equal(left_type_id, right_type_id, Variance::Covariant);

            ctx.infer.set_type(
                node_type_id,
                TypeKind::Empty, [],
                set,
                Reason::new(node_loc, "this assignment returns Empty"),
            );
        }
        NodeKind::Binary { op, left, right } => {
            let left = build_constraints(ctx, left, set);
            let right = build_constraints(ctx, right, set);
            ctx.infer.set_op_equal(op, left, right, node_type_id);
        }
        NodeKind::Reference(operand) => {
            let access = ctx.infer.add_empty_access(set);
            let inner = build_lvalue(ctx, operand, access, set);
            ctx.infer.set_type(
                node_type_id,
                TypeKind::Reference,
                [access, inner],
                set,
                Reason::new(node_loc, "of this reference operation"),
            );
        }
        NodeKind::Block {
            ref contents,
            label,
        } => {
            if let Some(label) = label {
                let label = ctx.locals.get_label_mut(label);
                label.type_infer_value_id = node_type_id;
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
                Reason::new(node_loc, "this break evaluates to an Empty type. Although it will in the future support evaluating to any type, the reason it doesn't is because of type ambiguities that can easily arise.")
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
            let compiler_type = ctx.infer.add_compiler_type(type_, set, Reason::new(node_loc, "of this type"));
            ctx.infer.set_equal(node_type_id, compiler_type, Variance::Invariant);
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

            let infer_type = type_infer::ValueKind::Type(Some(Type {
                kind: TypeKind::Function,
                args: Some(function_type_ids.into_boxed_slice()),
            }));
            let infer_type_id = ctx.infer.add(
                infer_type,
                set,
                Reason::new(node_loc, "of this type"),
            );
            ctx.infer
                .set_equal(infer_type_id, node_type_id, Variance::Invariant);
        }
        NodeKind::StructType { ref fields } => {
            // @Performance: Many allocations
            let names = fields.iter().map(|v| v.0).collect();
            let fields = fields.iter().map(|v| v.1).collect::<Vec<_>>();
            let fields = fields
                .into_iter()
                .map(|v| build_constraints(ctx, v, set))
                .collect();
            // @Performance: This could directly set the type in theory
            let temp = ctx.infer.add(
                type_infer::ValueKind::Type(Some(Type {
                    kind: type_infer::TypeKind::Struct(names),
                    args: Some(fields),
                })),
                set,
                Reason::new(node_loc, "of this type"),
            );
            ctx.infer.set_equal(node_type_id, temp, Variance::Invariant);
        }
        NodeKind::ReferenceType(inner, permits) => {
            let inner = build_constraints(ctx, inner, set);
            let access = permits_to_access(permits);
            let access = ctx.infer.add_access(Some(access), set, Reason::new(node_loc, "reference type access blah blah blah this reason shouldn't be seen, it has to be here right now because of technical crap I haven't cleaned up"));
            ctx.infer.set_type(
                node_type_id,
                TypeKind::Reference, [access, inner],
                set,
                Reason::new(node_loc, "of this reference type"),
            );
        }
        NodeKind::BufferType(inner, permits) => {
            let inner = build_constraints(ctx, inner, set);
            let access = permits_to_access(permits);
            let access = ctx.infer.add_access(Some(access), set, Reason::new(node_loc, "reference type access blah blah blah this reason shouldn't be seen, it has to be here right now because of technical crap I haven't cleaned up"));
            ctx.infer.set_type(
                node_type_id,
                TypeKind::Buffer, [access, inner],
                set,
                Reason::new(node_loc, "of this reference type"),
            );
        }
        _ => unimplemented!(
            "Ast node does not have a typing relationship yet {:?}",
            node.kind
        ),
    }

    node_type_id
}

fn permits_to_access(permits: Option<(Location, PtrPermits)>) -> type_infer::Access {
    permits.map_or_else(Default::default, |(loc, v)| {
        type_infer::Access::specific(
            v.read(),
            v.write(),
            Reason::new(loc, if v.read() {
                "it's defined as such here"
            } else {
                "these permissions don't include readability"
            }),
            Reason::new(
                if v.read() && v.write() {
                    loc.next_char()
                } else {
                    loc
                },
                if v.write() {
                    "it's defined as such here"
                } else {
                    "these permissions don't include mutability"
                },
            )
        )
    })
}

/// Normal values are assumed to be readonly, because they are temporaries, it doesn't really make sense to
/// write to them. However, in some cases the value isn't a temporary at all, but actually refers to a value
/// inside of another value. That's what this is for. Instead of forcing the value to be readonly, we can make
/// the readability/writability of the value depend on deeper values in the expression.
/// If this strategy doesn't work however, we fallback to read-only.
fn build_lvalue(
    ctx: &mut Context<'_, '_>,
    node_id: NodeId,
    access: type_infer::ValueId,
    set: ValueSetId,
) -> type_infer::ValueId {
    let node = ctx.ast.get(node_id);
    let node_loc = node.loc;
    let node_type_id = node.type_infer_value_id;

    match node.kind {
        NodeKind::Member { of, name } => {
            let of_type_id = build_lvalue(ctx, of, access, set);
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
        NodeKind::Parenthesis(inner) => {
            build_lvalue(ctx, inner, access, set);
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
            let value_type_id = build_lvalue(ctx, value, access, set);
            ctx.infer
                .set_equal(value_type_id, node_type_id, Variance::Invariant);
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
            operand,
        } => {
            let temp = ctx.infer.add_t(
                TypeKind::Reference,
                [access, node_type_id],
                set,
                Reason::new(node_loc, "it is dereferenced here"),
            );

            let operand_type_id = build_constraints(ctx, operand, set);
            ctx.infer
                .set_equal(operand_type_id, temp, Variance::Variant);
        }
        _ => {
            // Make it a reference to a temporary instead. This forces the pointer to be readonly.
            // @Speed: This could be faster...
            let access_strict = ctx.infer.add_access(
                Some(type_infer::Access::disallows(None, Some(Reason::new(node_loc, "temporary values are read-only")))),
                set,
                Reason::new(node_loc, "this isn't acceptable as an lvalue, so it's treated as a temporary value, and temporaries are read-only"),
            );
            ctx.infer
                .set_equal(access_strict, access, Variance::Invariant);
            return build_constraints(ctx, node_id, set);
        }
    }

    ctx.infer.set_value_set(node_type_id, set);
    ctx.infer.value_sets.add_node_to_set(set, node_id);

    node_type_id
}
