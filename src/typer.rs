use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::ir::Routine;
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::location::Location;
use crate::execution_time::ExecutionTime;
use crate::locals::{LocalVariables, LabelId};
use crate::operators::{BinaryOp, UnaryOp};
pub use crate::parser::{LocalUsage, Node, NodeKind, Ast, NodeView, TagKind};
use crate::ast::{NodeId, GenericChildIterator};
use crate::program::{PolyOrMember, PolyMemberId, Program, Task, constant::ConstantRef, BuiltinFunction, MemberId, MemberMetaData, FunctionId, FunctionMetaData, FunctionArgumentInfo, MemberKind, Builtin};
use crate::thread_pool::ThreadContext;
use crate::type_infer::{self, AstVariantId, ValueId as TypeId, Args, TypeSystem, ValueSetId, TypeKind, Reason, ReasonKind};
use crate::types::{self, IntTypeKind, UniqueTypeMarker, FunctionArgsBuilder};
use std::collections::HashMap;
use std::sync::Arc;
use ustr::Ustr;

pub const TARGET_COMPILER: u32 = 0x1;
pub const TARGET_NATIVE: u32 = 0x2;
pub const TARGET_ALL: u32 = 0xffff_ffff;

pub type AdditionalInfo = HashMap<(AstVariantId, NodeId), AdditionalInfoKind>;

#[derive(Clone)]
pub enum FunctionArgUsage {
    ValueOfAssign {
        function_arg: usize,
    },
    Value {
        function_arg: usize,
    },
    TupleElement {
        function_arg: usize,
        field: usize,
    },
}

#[derive(Clone)]
pub enum AdditionalInfoKind {
    FunctionCall(Vec<FunctionArgUsage>),
    Function(FunctionId),
    InferredConstant(TypeId),
    IsExpression(type_infer::ComparisonId),
    ConstIfResult(bool),
    ConstForAstVariants {
        referenced: bool,
        variant_ids: Vec<AstVariantId>,
    },
    Constant(ConstantRef),
    Monomorphised(MemberId),
}

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
    additional_info: AdditionalInfo,
    infer: TypeSystem,
    poly_params: Vec<PolyParam>,
    needs_explaining: Vec<(NodeId, type_infer::ValueId)>,
}

impl YieldData {
    pub fn insert_poly_params(&mut self, program: &Program, poly_args: &[crate::types::Type]) {
        let set = self.root_set_id;

        for (param, compiler_type) in self.poly_params.iter().zip(poly_args) {
            if param.is_type() {
                let type_id = self.infer.add_compiler_type(program, compiler_type, set);
                self.infer.set_equal(param.value_id, type_id, Reason::temp_zero());
            } else {
                let constant = self.infer.add_compiler_type(program, compiler_type, set);
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
    ast_variant_id: AstVariantId,
    additional_info: &'a mut AdditionalInfo,
    inside_type_comparison: bool,
    target_checker: TargetChecker,
}

#[derive(Clone)]
struct TargetCheck {
    loc: Location,
    subset: TypeId,
    superset: TypeId,
}

#[derive(Default, Clone)]
pub struct TargetChecker {
    checks: Vec<TargetCheck>,
    stack: Vec<TypeId>,
}

pub fn process_ast<'a>(
    errors: &mut ErrorCtx,
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    locals: LocalVariables,
    ast: Ast,
    member_kind: MemberKind,
) -> Result<(Result<(DependencyList, LocalVariables, TypeSystem, Ast, TypeId, AdditionalInfo), (DependencyList, YieldData)>, MemberMetaData), ()> {
    profile::profile!("typer::process_ast");
    let (mut yield_data, meta_data) = begin(errors, thread_context, program, locals, ast, Vec::new(), member_kind);
    solve(errors, thread_context, program, &mut yield_data);
    finish(errors, yield_data).map(|v| (v, meta_data))
}

pub fn begin<'a>(
    errors: &mut ErrorCtx,
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    mut locals: LocalVariables,
    ast: Ast,
    poly_params: Vec<(Location, Ustr)>,
    member_kind: MemberKind,
) -> (YieldData, MemberMetaData) {
    let mut emit_deps = DependencyList::new();
    let mut infer = TypeSystem::new(ast.structure.len());

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

    let mut needs_explaining = Vec::new();
    let mut additional_info = Default::default();
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
        ast_variant_id: AstVariantId::root(),
        additional_info: &mut additional_info,
        inside_type_comparison: false,
        target_checker: TargetChecker::default(),
    };

    // Build the type relationships between nodes.
    let root_set_id = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);

    let node = ast.root();
    let (root_value_id, meta_data) = match node.kind {
        NodeKind::FunctionDeclaration { .. } => {
            let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);
            ctx.infer.set_value_set(node_type_id, root_set_id);
            ctx.infer.value_sets.add_node_to_set(root_set_id, ctx.ast_variant_id, node.id);
            let mut meta_data = FunctionMetaData::default();
            build_function_declaration(&mut ctx, node, root_set_id, Some(&mut meta_data));

            (node_type_id, MemberMetaData::Function(meta_data))
        }
        _ => (
            match member_kind {
                MemberKind::Type { is_aliased: false } => {
                    build_unique_type(&mut ctx, node, root_set_id, UniqueTypeMarker { name: Some(ast.name), loc: node.loc })
                }
                MemberKind::Type { is_aliased: true } => {
                    build_type(&mut ctx, node, root_set_id)
                }
                MemberKind::Const => {
                    build_constraints(&mut ctx, node, root_set_id)
                }
            },
            MemberMetaData::None,
        )
    };

    let target_checker = ctx.target_checker;
    let value_set = infer.value_sets.get_mut(root_set_id);
    value_set.emit_deps = Some(emit_deps);
    value_set.target_checker = Some(target_checker);

    (
        YieldData {
            root_set_id,
            root_value_id,
            ast,
            locals,
            infer,
            poly_params,
            needs_explaining,
            additional_info,
        },
        meta_data,
    )
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
        ast_variant_id: AstVariantId::root(),
        additional_info: &mut data.additional_info,
        inside_type_comparison: false,
        target_checker: TargetChecker::default(),
    };

    loop {
        ctx.infer.solve();

        let mut progress = false;
        for value_set_id in ctx.infer.value_sets.iter_ids() {
            let value_set = ctx.infer.value_sets.get_mut(value_set_id);
            if value_set.has_errors
            || value_set.has_been_computed
            || value_set.uncomputed_values() > 0
            {
                continue;
            }

            debug_assert_eq!(value_set.uncomputed_values(), 0, "The number of uncomputed values cannot be less than zero");

            let related_nodes = std::mem::take(&mut value_set.related_nodes);

            let value_set = ctx.infer.value_sets.get_mut(value_set_id);
            value_set.related_nodes = related_nodes;
            value_set.has_been_computed = true;
            let waiting_on = std::mem::replace(&mut value_set.waiting_on_completion, WaitingOnTypeInferrence::None);

            let mut has_errors = value_set.has_errors;
            
            let value_set = ctx.infer.value_sets.get(value_set_id);
            if let Some(target_checker) = &value_set.target_checker {
                if validate(ctx.infer, ctx.errors, target_checker) {
                    has_errors = true;
                }
            }

            if !has_errors {
                subset_was_completed(&mut ctx, &mut data.ast, waiting_on, value_set_id);
            }

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
) -> Result<Result<(DependencyList, LocalVariables, TypeSystem, Ast, TypeId, AdditionalInfo), (DependencyList, YieldData)>, ()> {
    for (node_id, needs_explaining) in from.needs_explaining {
        for chain in type_infer::get_reasons(needs_explaining, &from.infer, &from.ast) {
            chain.output(errors, &from.ast, &from.infer);
            errors.note(from.ast.get(node_id).loc, format!("The type is `{}` because...", from.infer.value_to_str(needs_explaining, 0)));
        }
    }

    let mut are_incomplete_sets = false;
    // We only care about the base set.
    for value_set_id in from.infer.value_sets.iter_ids().take(1) {
        let value_set = from.infer.value_sets.get(value_set_id);
        if value_set.has_errors || value_set.uncomputed_values() > 0 {
            errors.global_error(format!("Set {} is uncomputable! (uncomputability doesn't have a proper error yet, this is temporary)", value_set_id));
            are_incomplete_sets = true;
        }
    }

    if from.infer.output_errors(errors, &from.ast) {
        return Err(());
    } else if are_incomplete_sets {
        from.infer.output_incompleteness_errors(errors, &from.ast);
        return Err(());
    }

    let emit_deps = from.infer.value_sets.get_mut(from.root_set_id).emit_deps.take().unwrap();

    Ok(Ok((emit_deps, from.locals, from.infer, from.ast, from.root_value_id, from.additional_info)))
}

fn subset_was_completed(ctx: &mut Context<'_, '_>, ast: &mut Ast, waiting_on: WaitingOnTypeInferrence, set: ValueSetId) {
    match waiting_on {
        WaitingOnTypeInferrence::ConstFor { node_id, ast_variant_id, parent_set, runs, iterator_type } => {
            let node = ast.get(node_id);
            let [iterator, _i_value, mut inner, _else_body] = node.children.into_array();

            let mut iterator_type = ctx.infer.get(iterator_type);

            let mut referenced = false;
            if matches!(iterator_type.kind(), TypeKind::Reference) {
                iterator_type = ctx.infer.get(iterator_type.args()[0]);
                referenced = true;
            }

            if !matches!(iterator_type.kind(), TypeKind::Tuple) {
                ctx.errors.error(iterator.loc, "Constant for loops can only iterate over tuples or references of tuples".to_string());
                return;
            }

            let iterator_args: Vec<_> = if referenced {
                iterator_type.args().to_vec().into_iter().map(|v| {
                    ctx.infer.add_type(TypeKind::Reference, Args([(v, Reason::temp(node.loc))]), parent_set)
                }).collect()
            } else {
                iterator_type.args().to_vec()
            };

            let mut emit_deps = ctx.infer.value_sets.get_mut(parent_set).emit_deps.take().unwrap_or_default();
            let mut sub_ctx = Context {
                thread_context: ctx.thread_context,
                errors: ctx.errors,
                program: ctx.program,
                locals: ctx.locals,
                emit_deps: &mut emit_deps,
                poly_params: ctx.poly_params,
                infer: ctx.infer,
                needs_explaining: ctx.needs_explaining,
                runs,
                ast_variant_id: AstVariantId::invalid(),
                additional_info: ctx.additional_info,
                inside_type_comparison: false,
                // TODO: This is incorrect, we're going to change things up a lot later.
                target_checker: TargetChecker::default(),
            };

            let mut variant_ids = Vec::with_capacity(iterator_args.len());
            for iterator_arg in iterator_args {
                let sub_variant_id = sub_ctx.infer.values.add_ast_variant(ast_variant_id, inner.subtree_region());
                sub_ctx.ast_variant_id = sub_variant_id;
                variant_ids.push(sub_variant_id);

                let [v_value_decl, body] = inner.children.borrow().into_array();

                let v_value_id = build_declarative_lvalue(&mut sub_ctx, v_value_decl, parent_set, true);
                sub_ctx.infer.set_equal(iterator_arg, v_value_id, Reason::temp(node.node.loc));

                build_constraints(&mut sub_ctx, body, parent_set);
            }

            ctx.infer.value_sets.get_mut(parent_set).emit_deps = Some(emit_deps);
            ctx.additional_info.insert((ast_variant_id, node_id), AdditionalInfoKind::ConstForAstVariants { referenced, variant_ids });

            ctx.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::ConditionalCompilation { node_id, condition, true_body, false_body, ast_variant_id, parent_set, runs } => {
            let loc = ast.get(condition).loc;
            let result = match crate::interp::emit_and_run(
                ctx.thread_context,
                ctx.program,
                ctx.locals,
                ctx.infer,
                ast,
                ctx.additional_info,
                condition,
                ast_variant_id,
                &mut vec![loc],
            ) {
                Ok(constant_ref) => {
                    unsafe { *constant_ref.as_ptr().cast::<u8>() > 0 }
                }
                Err((message, call_stack)) => {
                    for &caller in call_stack.iter().rev().skip(1) {
                        ctx.errors.info(caller, "".to_string());
                    }

                    ctx.errors.error(*call_stack.last().unwrap(), message);
                    ctx.infer.value_sets.get_mut(set).has_errors = true;

                    return;
                }
            };
            
            let emitting = if result { true_body } else { false_body };

            let mut emit_deps = ctx.infer.value_sets.get_mut(parent_set).emit_deps.take().unwrap_or_default();
            let mut sub_ctx = Context {
                thread_context: ctx.thread_context,
                errors: ctx.errors,
                program: ctx.program,
                locals: ctx.locals,
                emit_deps: &mut emit_deps,
                poly_params: ctx.poly_params,
                infer: ctx.infer,
                needs_explaining: ctx.needs_explaining,
                runs,
                ast_variant_id: ast_variant_id,
                additional_info: ctx.additional_info,
                inside_type_comparison: false,
                // TODO: This is not correct...
                target_checker: TargetChecker::default(),
            };

            let child_type = build_constraints(&mut sub_ctx, ast.get(emitting), parent_set);
            ctx.infer.value_sets.get_mut(parent_set).emit_deps = Some(emit_deps);
            ctx.infer.set_equal(TypeId::Node(ast_variant_id, node_id), child_type, Reason::temp_zero());

            ctx.additional_info.insert((ast_variant_id, node_id), AdditionalInfoKind::ConstIfResult(result));
            ctx.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::ConstantFromValueId { value_id, to, ast_variant_id, parent_set } => {
            // We expect the type to already be checked by some other mechanism,
            // e.g., node_type_id should be equal to the type of the constant.
            let constant_ref = ctx.infer.extract_constant_temp(value_id).unwrap();

            ctx.additional_info.insert((ast_variant_id, to), AdditionalInfoKind::Constant(constant_ref));
            ctx.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::SizeOf { parent_set } => {
            ctx.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::MonomorphiseMember { node_id, poly_member_id, when_needed, params, parent_set, ast_variant_id } => {
            let node_loc = ast.get(node_id).loc;
            let mut fixed_up_params = Vec::with_capacity(params.len());

            for param in params {
                fixed_up_params.push(ctx.infer.value_to_compiler_type(param));
            }

            let wanted_dep = match when_needed {
                ExecutionTime::Typing => MemberDep::ValueAndCallableIfFunction,
                _ => MemberDep::Type,
            };

            ctx.infer.value_sets.unlock(parent_set);

            if let Ok(member_id) = ctx.program.monomorphise_poly_member(ctx.errors, ctx.thread_context, poly_member_id, &fixed_up_params, wanted_dep) {
                let type_ = ctx.program.get_member_type(member_id);

                let compiler_type = ctx.infer.add_compiler_type(ctx.program, &type_, parent_set);
                ctx.infer.set_equal(TypeId::Node(ast_variant_id, node_id), compiler_type, Reason::new(node_loc, ReasonKind::IsOfType));

                ctx.additional_info.insert((ast_variant_id, node_id), AdditionalInfoKind::Monomorphised(member_id));

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
        WaitingOnTypeInferrence::ValueIdFromConstantComputation { computation, value_id, ast_variant_id } => {
            let len_loc = ast.get(computation).loc;
            match crate::interp::emit_and_run(
                ctx.thread_context,
                ctx.program,
                ctx.locals,
                ctx.infer,
                ast,
                ctx.additional_info,
                computation,
                ast_variant_id,
                &mut vec![len_loc],
            ) {
                Ok(constant_ref) => {
                    let computation_node = ast.get(computation);
                    let finished_value = ctx.infer.add_value(TypeId::Node(ctx.ast_variant_id, computation), constant_ref, set);

                    ctx.infer.set_equal(finished_value, value_id, Reason::new(computation_node.loc, ReasonKind::IsOfType));
                }
                Err((message, call_stack)) => {
                    for &caller in call_stack.iter().rev().skip(1) {
                        ctx.errors.info(caller, "".to_string());
                    }

                    ctx.errors.error(*call_stack.last().unwrap(), message);
                    ctx.infer.value_sets.get_mut(set).has_errors = true;
                }
            }
        }
        WaitingOnTypeInferrence::FunctionDeclaration {
            node_id,
            is_extern,
            function_type,
            parent_set,
            time,
            ast_variant_id,
        } => {
            let node_loc = ast.get(node_id).loc;
            let function_id = ctx.program.insert_function(node_loc);

            let type_ = ctx.infer.value_to_compiler_type(function_type);
            let emit_deps = ctx.infer.value_sets.get_mut(set).emit_deps.take().unwrap();

            if let Some(symbol_name) = is_extern {
                ctx.program.add_external_symbol(symbol_name);

                let routine = Routine::Extern(symbol_name);

                ctx.thread_context.emitters.emit_routine(ctx.program, function_id, &routine);
                ctx.program.set_routine_of_function(function_id, Vec::new(), routine);
            } else {
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
                                ctx.additional_info.clone(),
                                ast.clone(),
                                node_id,
                                type_,
                                function_id,
                                ast_variant_id,
                            ),
                        );
                    }
                    ExecutionTime::Typing => {
                        crate::emit::emit_function_declaration(
                            ctx.thread_context,
                            ctx.program,
                            ctx.locals,
                            ctx.infer,
                            ast.get(node_id),
                            ctx.additional_info,
                            node_id,
                            ast_variant_id,
                            node_loc,
                            function_id,
                            true,
                        );
                    }
                }
            }

            ctx.additional_info.insert((ast_variant_id, node_id), AdditionalInfoKind::Function(function_id));
            ctx.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::BuiltinFunctionInTyping {
            node_id,
            function,
            parent_set,
            ast_variant_id,
        } => {
            let node = ast.get(node_id);
            let node_loc = node.loc;

            let function_id = ctx.program.insert_defined_function(
                node_loc,
                Vec::new(),
                crate::ir::Routine::Builtin(function),
            );

            let routine = ctx.program.get_routine(function_id).unwrap();
            ctx.thread_context.emitters.emit_routine(ctx.program, function_id, &routine);

            ctx.additional_info.insert((ast_variant_id, node_id), AdditionalInfoKind::Function(function_id));
            ctx.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::None => {},
    }
}

fn validate(types: &TypeSystem, errors: &mut ErrorCtx, target_checker: &TargetChecker) -> bool {
    let mut has_errors = false;

    for check in &target_checker.checks {
        let &TypeKind::ConstantValue(subset) = types.get(check.subset).kind() else { panic!() };
        let &TypeKind::ConstantValue(superset) = types.get(check.superset).kind() else { panic!() };

        let subset_value   = unsafe { *subset.as_ptr().cast::<u32>() };
        let superset_value = unsafe { *superset.as_ptr().cast::<u32>() };

        if (superset_value & subset_value) != subset_value {
            has_errors = true;
            errors.error(check.loc, "Target mismatch (temporary error message)".to_string());
        }
    }

    has_errors
}

fn build_constraints(
    ctx: &mut Context<'_, '_>,
    node: NodeView<'_>,
    set: ValueSetId,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    ctx.infer.set_value_set(node_type_id, set);
    ctx.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, node.id);

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
                ast_variant_id: ctx.ast_variant_id,
            });
        }
        NodeKind::AnonymousMember { name } => {
            ctx.infer.value_sets.lock(set);
            let sub_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);
            let unknown = ctx.infer.add_unknown_type_with_set(sub_set);
            let value = ctx.infer.add_type(TypeKind::Constant, Args([(node_type_id, Reason::temp(node_loc)), (unknown, Reason::temp(node_loc))]), sub_set);
            ctx.infer.set_constant_field(unknown, name, node_type_id, Reason::temp(node_loc));
            ctx.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::ConstantFromValueId {
                value_id: value,
                to: node.id,
                parent_set: set,
                ast_variant_id: ctx.ast_variant_id,
            });
        }
        NodeKind::Is => {
            let [expr, type_] = node.children.into_array();

            let got = build_type(ctx, expr, set);

            let subset = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);
            let old_inside_type_comparison = ctx.inside_type_comparison;
            ctx.inside_type_comparison = true;
            let wanted = build_type(ctx, type_, subset);
            ctx.inside_type_comparison = old_inside_type_comparison;

            let comparison_id = ctx.infer.add_comparison(set, got, wanted);

            ctx.additional_info.insert((ctx.ast_variant_id, node.id), AdditionalInfoKind::IsExpression(comparison_id));

            ctx.infer.set_type(node_type_id, TypeKind::Bool, Args([]), set);
        }
        NodeKind::Tuple => {
            let mut values = Vec::with_capacity(node.children.len());
            for child in node.children {
                let child_id = build_constraints(ctx, child, set);
                values.push((child_id, Reason::temp(node_loc)));
            }

            ctx.infer.set_type(node_type_id, TypeKind::Tuple, Args(values), set);
        }
        NodeKind::Explain => {
            let [inner] = node.children.into_array();
            let inner = build_constraints(ctx, inner, set);
            ctx.infer.set_equal(node_type_id, inner, Reason::new(node_loc, ReasonKind::Passed));
            ctx.needs_explaining.push((node.id, inner));
        }
        NodeKind::Pack => {
            let [inner] = node.children.into_array();
            let inner_type = build_constraints(ctx, inner, set);
            ctx.infer.set_pack(node_type_id, inner_type, Reason::temp(node_loc));
        }
        NodeKind::Unpack => {
            let [inner] = node.children.into_array();
            let inner_type = build_constraints(ctx, inner, set);
            ctx.infer.set_pack(inner_type, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::SizeOf => {
            let [inner] = node.children.into_array();
            let subset = ctx.infer.value_sets.add(WaitingOnTypeInferrence::SizeOf { parent_set: set });
            build_type(ctx, inner, subset);

            ctx.infer.set_int(node_type_id, IntTypeKind::Usize, set);

            ctx.infer.value_sets.lock(set);
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

            ctx.infer.set_value_set(TypeId::Node(ctx.ast_variant_id, on.id), set);
            ctx.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, on.id);
            ctx.infer.set_equal(TypeId::Node(ctx.ast_variant_id, on.id), node_type_id, Reason::temp(node_loc));

            let id = ctx.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");
            build_global(ctx, node.id, node.node, node.loc, id, Some(children), set, false);
        }
        NodeKind::Global { scope, name } => {
            let id = ctx.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");
            build_global(ctx, node.id, node.node, node.loc, id, None, set, false);
        }
        NodeKind::While {
            label: label_id,
        } => {
            let [iteration_var, condition, body, else_body] = node.children.into_array();

            let iteration_var_id = build_declarative_lvalue(ctx, iteration_var, set, true);

            let label = ctx.locals.get_label_mut(label_id);
            label.stack_frame_id = set;
            label.declared_at = Some(else_body.id);

            ctx.infer.set_int(iteration_var_id, IntTypeKind::Usize, set);

            let condition_type_id = build_constraints(ctx, condition, set);
            let bool_type = ctx.infer.add_type(TypeKind::Bool, Args([]), set);
            ctx.infer.set_equal(condition_type_id, bool_type, Reason::new(node_loc, ReasonKind::IsOfType));

            build_constraints(ctx, body, set);

            let else_type = build_constraints(ctx, else_body, set);

            ctx.infer.set_equal(node_type_id, else_type, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::For {
            is_const: Some(_),
            label: label_id,
        } => {
            let [iterating, i_value, _inner, else_body] = node.children.into_array();

            let iteration_var_id = build_declarative_lvalue(ctx, i_value, set, true);

            let label = ctx.locals.get_label_mut(label_id);
            label.stack_frame_id = set;
            label.declared_at = Some(else_body.id);

            let usize_id = ctx.infer.add_int(IntTypeKind::Usize, set);
            ctx.infer.set_equal(iteration_var_id, usize_id, Reason::temp(node_loc));

            let iterator_type = build_constraints(ctx, iterating, set);

            let check_type = ctx.infer.add_unknown_type();
            let sub_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::ConstFor {
                node_id: node.id,
                ast_variant_id: ctx.ast_variant_id,
                iterator_type: check_type,
                runs: ctx.runs,
                parent_set: set,
            });
            ctx.infer.set_value_set(check_type, sub_set);
            ctx.infer.set_equal(check_type, iterator_type, Reason::new(node_loc, ReasonKind::Passed));

            ctx.infer.value_sets.lock(set);

            let else_type = build_constraints(ctx, else_body, set);
            ctx.infer.set_equal(node_type_id, else_type, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::For {
            is_const: None,
            label: label_id,
        } => {
            let [iterating, iteration_var, inner, else_body] = node.children.into_array();
            let [iterator, body] = inner.children.into_array();

            let iteration_var_id = build_declarative_lvalue(ctx, iteration_var, set, true);
            let iterator_id = build_declarative_lvalue(ctx, iterator, set, true);

            let label = ctx.locals.get_label_mut(label_id);
            label.stack_frame_id = set;
            label.declared_at = Some(else_body.id);

            let usize_id = ctx.infer.add_int(IntTypeKind::Usize, set);
            ctx.infer.set_equal(iteration_var_id, usize_id, Reason::temp(node_loc));

            // The type the body returns doesn't matter, since we don't forward it.
            let iterating_type_id = build_constraints(ctx, iterating, set);

            build_constraints(ctx, body, set);

            ctx.infer.set_for_relation(iterator_id, iterating_type_id, Reason::temp(node_loc));

            let else_type = build_constraints(ctx, else_body, set);

            ctx.infer.set_equal(node_type_id, else_type, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::Literal(Literal::Float(_)) => {
            ctx.infer.set_type(node_type_id, TypeKind::Float, (), set);
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
        NodeKind::Literal(Literal::String(_)) => {
            let u8_type = ctx.infer.add_int(IntTypeKind::U8, set);
            ctx.infer.set_type(node_type_id, TypeKind::Buffer, Args([(u8_type, Reason::temp(node_loc))]), set);
        }
        NodeKind::BuiltinFunction(function) => {
            let function_type_id = ctx.infer.add_unknown_type();
            let sub_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::BuiltinFunctionInTyping {
                node_id: node.id,
                function,
                parent_set: set,
                ast_variant_id: ctx.ast_variant_id,
            });

            // The parent value set has to wait for this function declaration to be emitted until
            // it can continue, so we lock it to make sure it doesn't get emitted before then.
            ctx.infer.value_sets.lock(set);

            ctx.infer.set_type(function_type_id, TypeKind::Function, (), sub_set);
            ctx.infer.set_equal(node_type_id, function_type_id, Reason::new(node_loc, ReasonKind::IsOfType));
        }
        NodeKind::ArrayLiteral => {
            let inner_type = ctx.infer.add_unknown_type_with_set(set);

            for arg in node.children.into_iter() {
                let arg_type_id = build_constraints(ctx, arg, set);
                ctx.infer.set_equal(arg_type_id, inner_type, Reason::new(node_loc, ReasonKind::Passed));
            }

            let usize = ctx.infer.add_int(IntTypeKind::Usize, set);
            let length = ctx.program.insert_buffer(&types::Type::new_int(IntTypeKind::Usize), (node.children.len()).to_le_bytes().as_ptr());

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
        NodeKind::Local { local_id, .. } => {
            let local = ctx.locals.get(local_id);
            let local_type_id = TypeId::Node(ctx.ast_variant_id, local.declared_at.unwrap());
            ctx.infer
                .set_equal(local_type_id, node_type_id, Reason::new(node_loc, ReasonKind::LocalVariableIs(local.name)));

            if ctx.runs != ExecutionTime::Never && local.stack_frame_id != set {
                ctx.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type". to_string());
                ctx.infer.value_sets.get_mut(set).has_errors = true;
            }
        }
        NodeKind::If => {
            let [tags, condition, true_body, else_body] = node.children.into_array();

            let mut tags = build_tags(ctx, tags, set);

            if let Some(_) = tags.compile.take() {
                let sub_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::ConditionalCompilation {
                    node_id: node.id,
                    condition: condition.id,
                    true_body: true_body.id,
                    false_body: else_body.id,
                    ast_variant_id: ctx.ast_variant_id,
                    parent_set: set,
                    runs: ctx.runs,
                });
                ctx.infer.value_sets.lock(set);

                let old_runs = ctx.runs;
                ctx.runs = ctx.runs.combine(ExecutionTime::Typing);
                let condition_type_id = build_constraints(ctx, condition, sub_set);
                ctx.runs = old_runs;
                let condition_type = ctx.infer.add_type(TypeKind::Bool, Args([]), sub_set);
                ctx.infer
                    .set_equal(condition_type_id, condition_type, Reason::new(node_loc, ReasonKind::IsOfType));
            } else {
                let condition_type_id = build_constraints(ctx, condition, set);
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

            tags.finish(ctx, set);
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
        NodeKind::FunctionDeclaration { .. } => {
            build_function_declaration(ctx, node, set, None);
        }
        NodeKind::ExpressiveFunctionCall => {
            let mut children = node.children.into_iter();
            let first_arg = children.next().unwrap();

            let calling = children.next().unwrap();
            let calling_type_id = TypeId::Node(ctx.ast_variant_id, calling.id);
            let meta_data = build_with_metadata(ctx, calling, set);

            build_function_call(
                ctx,
                node.id,
                node_type_id,
                node_loc,
                calling_type_id,
                meta_data,
                std::iter::once(first_arg).chain(children),
                set,
            );
        }
        NodeKind::FunctionCall => {
            let mut children = node.children.into_iter();

            let calling = children.next().unwrap();
            let calling_type_id = TypeId::Node(ctx.ast_variant_id, calling.id);
            let meta_data = build_with_metadata(ctx, calling, set);

            build_function_call(
                ctx,
                node.id,
                node_type_id,
                node_loc,
                calling_type_id,
                meta_data,
                children,
                set,
            );
        }
        NodeKind::Binary {
            op: BinaryOp::Assign,
        } => {
            let [left, right] = node.children.into_array();
            let left_type_id = build_declarative_lvalue(ctx, left, set, false);
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

            // TODO: This is a massive hack! We want this to exist in the type inferrer itself probably....
            if op == BinaryOp::Equals || op == BinaryOp::NotEquals || op == BinaryOp::BitAnd || op == BinaryOp::BitOr {
                ctx.infer.set_equal(left, right, Reason::temp(node_loc));
            }

            ctx.infer.set_op_equal(op, left, right, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::Reference => {
            let [operand] = node.children.into_array();
            let inner = build_lvalue(ctx, operand, set, true);
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
            if let Some(label_id) = label {
                let label = ctx.locals.get_label_mut(label_id);
                label.stack_frame_id = set;
                label.declared_at = node.children.into_iter().last().map(|v| v.id);
            }

            let mut children = node.children.into_iter();
            let tags_node = children.next().unwrap();
            let mut tags = build_tags(ctx, tags_node, set);
            let target_based = if let Some((tag_loc, target)) = tags.target.take() {
                let required_type = ctx.infer.add_type(TypeKind::Empty, Args([]), set);
                ctx.infer.set_equal(node_type_id, required_type, Reason::temp(tag_loc));

                if let Some(&parent) = ctx.target_checker.stack.last() {
                    ctx.target_checker.checks.push(TargetCheck {
                        loc: tag_loc,
                        subset: target,
                        superset: parent,
                    });
                }
                ctx.target_checker.stack.push(target);
                true
            } else {
                false
            };
            tags.finish(ctx, set);

            let children_len = children.len();
            for statement_id in children.by_ref().take(children_len - 1) {
                build_constraints(ctx, statement_id, set);
            }

            let last_type_id = build_constraints(ctx, children.next().unwrap(), set);
            ctx.infer
                .set_equal(node_type_id, last_type_id, Reason::new(node_loc, ReasonKind::Passed));

            if target_based {
                ctx.target_checker.stack.pop();
            }
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

            let label_type_id = TypeId::Node(ctx.ast_variant_id, label.declared_at.unwrap());

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
        NodeKind::Unary { op: _ } => {
            // @TODO: Make sure the types are valid for the operator
            let [operand] = node.children.into_array();
            let operand_id = build_constraints(ctx, operand, set);

            ctx.infer.set_equal(operand_id, node_type_id, Reason::temp(node_loc));
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
        ref kind => {
            ctx.errors.error(node_loc, format!("Invalid expression(it might only be valid as an lvalue, or as a type) {:?}", kind));
            ctx.infer.value_sets.get_mut(set).has_errors |= true;
        }
    }

    node_type_id
}

fn extract_name(ctx: &Context<'_, '_>, node: NodeView<'_>) -> Option<(Ustr, Location)> {
    match node.kind {
        NodeKind::Local { local_id, .. } => {
            Some((ctx.locals.get(local_id).name, node.loc))
        }
        NodeKind::TypeBound => {
            let [value, _] = node.children.into_array();
            extract_name(ctx, value)
        }
        _ => None,
    }
}

#[derive(Default, Debug, Clone)]
struct Tags {
    calling_convention: Option<(Location, TypeId)>,
    target: Option<(Location, TypeId)>,
    compile: Option<Location>,
    label: Option<(Location, LabelId, TypeId)>,
}

impl Tags {
    fn finish(self, ctx: &mut Context<'_, '_>, set: ValueSetId) {
        if let Some((loc, _)) = self.calling_convention {
            ctx.errors.error(loc, format!("Tag not valid for this kind of expression"));
            ctx.infer.value_sets.get_mut(set).has_errors = true;
        }

        if let Some((loc, _)) = self.target {
            ctx.errors.error(loc, format!("Tag not valid for this kind of expression"));
            ctx.infer.value_sets.get_mut(set).has_errors = true;
        }

        if let Some((loc, _, _)) = self.label {
            ctx.errors.error(loc, format!("Tag not valid for this kind of expression"));
            ctx.infer.value_sets.get_mut(set).has_errors = true;
        }

        if let Some(loc) = self.compile {
            ctx.errors.error(loc, format!("Tag not valid for this kind of expression"));
            ctx.infer.value_sets.get_mut(set).has_errors = true;
        }
    }
}

fn build_tags(
    ctx: &mut Context<'_, '_>,
    node: NodeView<'_>,
    set: ValueSetId,
) -> Tags {
    // TODO: The double-definition checks here are redundant; we could do them easier in the parser
    // probably, so we should do them there. Also, I don't think it's very useful to pick a default here,
    // since first of all, this is an uncommon mistake, so not showing more errors might be fine.

    let mut tags = Tags::default();

    for node in node.children.into_iter() {
        let &NodeKind::Tag(tag_kind) = &node.kind else { unreachable!("Invalid tag list") };

        match tag_kind {
            TagKind::CallingConvention => {
                let [inner] = node.children.into_array();
                if let Some(_) = tags.calling_convention {
                    ctx.errors.error(node.loc, format!("`call` defined twice"));
                    ctx.infer.value_sets.get_mut(set).has_errors |= true;
                }
                let value = build_inferrable_constant_value(ctx, inner, set);

                let builtin_id = ctx.program
                    .get_member_id_from_builtin(Builtin::CallingConvention)
                    .expect("Parser should make sure we have access to calling convention");
                // TODO: It is scary to monomorphise something like this, since we have to give a node
                // that is the "global". Maybe there should be an entirely different code path for types?
                build_global(ctx, inner.id, inner.node, inner.loc, builtin_id, None, set, true);

                tags.calling_convention = Some((
                    node.loc,
                    value.constant_value,
                ));
            }
            TagKind::Target => {
                let [inner] = node.children.into_array();
                if let Some(_) = tags.target {
                    ctx.errors.error(node.loc, format!("`target` defined twice"));
                    ctx.infer.value_sets.get_mut(set).has_errors |= true;
                }
                let value = build_inferrable_constant_value(ctx, inner, set);

                let builtin_id = ctx.program
                    .get_member_id_from_builtin(Builtin::Target)
                    .expect("Parser should make sure we have access to target");
                // TODO: It is scary to monomorphise something like this, since we have to give a node
                // that is the "global". Maybe there should be an entirely different code path for types?
                build_global(ctx, inner.id, inner.node, inner.loc, builtin_id, None, set, true);

                ctx.additional_info.insert((ctx.ast_variant_id, node.id), AdditionalInfoKind::InferredConstant(value.constant_value));

                tags.target = Some((
                    node.loc,
                    value.constant_value,
                ));
            }
            TagKind::Compile => {
                if let Some(_) = tags.compile {
                    ctx.errors.error(node.loc, format!("`const` defined twice"));
                    ctx.infer.value_sets.get_mut(set).has_errors |= true;
                }

                tags.compile = Some(node.loc);
            }
            TagKind::Label(label_id) => {
                ctx.locals.get_label_mut(label_id).declared_at = Some(node.id);
                tags.label = Some((node.loc, label_id, TypeId::Node(ctx.ast_variant_id, node.id)));
            }
        }
    }

    tags
}

fn build_function_declaration(
    ctx: &mut Context<'_, '_>,
    node: NodeView<'_>,
    set: ValueSetId,
    mut wants_meta_data: Option<&mut FunctionMetaData>,
) {
    let &NodeKind::FunctionDeclaration { ref is_extern, ref argument_infos } = &node.node.kind else { unreachable!() };

    let sub_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);

    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

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
        ast_variant_id: ctx.ast_variant_id,
        additional_info: ctx.additional_info,
        inside_type_comparison: false,
        target_checker: TargetChecker::default(),
    };

    let mut children = node.children.into_iter();
    let mut tags = build_tags(&mut sub_ctx, children.next().unwrap(), sub_set);

    sub_ctx.infer.value_sets.lock(set);

    let num_children = children.len();

    // @Cleanup: This isn't that nice
    let num_args = num_children - if is_extern.is_some() { 1 } else { 2 };

    if let Some(meta_data) = wants_meta_data.as_mut() {
        meta_data.arguments = Vec::with_capacity(num_args);
    }

    let mut function_args = FunctionArgsBuilder::with_num_args_capacity(num_args);
    for (argument_info, argument) in argument_infos.iter().zip(children.by_ref().take(num_args)) {
        let decl_id = build_declarative_lvalue(&mut sub_ctx, argument, sub_set, true);
        function_args.add_arg((decl_id, Reason::temp(node.node.loc)));

        if let Some(meta_data) = wants_meta_data.as_mut() {
            meta_data.arguments.push(FunctionArgumentInfo {
                name: extract_name(&sub_ctx, argument),
                var_args: argument_info.var_args,
            });
        } else {
            if let Some(loc) = argument_info.var_args {
                sub_ctx.errors.error(loc, format!("Cannot define var_args in this function, because it isn't bound to a constant (thus the var_args are lost)"));
                sub_ctx.infer.value_sets.get_mut(set).has_errors |= true;
            }
        }
    }

    let returns = children.next().unwrap();
    let returns_type_reason = Reason::new(returns.loc, ReasonKind::FunctionDeclReturnType);
    let returns_loc = returns.loc;
    let returns_type_id = build_type(&mut sub_ctx, returns, sub_set);
    function_args.set_return((returns_type_id, returns_type_reason));

    if let Some((loc, target)) = tags.target.take() {
        function_args.set_target((target, Reason::temp(loc)));
        sub_ctx.target_checker.stack.push(target);
    } else {
        // TODO: This should be the borkle calling convention
        let constant_value = sub_ctx.program.insert_buffer(&types::Type::new_int(IntTypeKind::U32), (&TARGET_ALL) as *const u32 as *const u8);
        let target = sub_ctx.infer.add_type(TypeKind::ConstantValue(constant_value), Args([]), set);
        function_args.set_target((target, Reason::temp(node.loc)));
    };

    if is_extern.is_none() {
        let body = children.next().unwrap();
        let body_type_id = build_constraints(&mut sub_ctx, body, sub_set);

        sub_ctx.infer
            .set_equal(body_type_id, returns_type_id, Reason::new(returns_loc, ReasonKind::FunctionDeclReturned));
    };

    let target_checker = sub_ctx.target_checker;

    if let Some((loc, calling_convention)) = tags.calling_convention.take() {
        function_args.set_calling_convention((calling_convention, Reason::temp(loc)));
    } else {
        // TODO: This should be the borkle calling convention
        let constant_value = ctx.program.insert_buffer(&types::Type::new_int(IntTypeKind::U8), (&0_u8) as *const u8);
        let calling_convention = ctx.infer.add_type(TypeKind::ConstantValue(constant_value), Args([]), set);
        function_args.set_calling_convention((calling_convention, Reason::temp(node.loc)));
    }

    tags.finish(ctx, sub_set);
    
    let infer_type_id = ctx.infer.add_type(TypeKind::Function, Args(function_args.build()), sub_set);
    ctx.infer
        .set_equal(infer_type_id, node_type_id, Reason::new(node.node.loc, ReasonKind::FunctionDecl));

    ctx.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::FunctionDeclaration {
        node_id: node.id,
        is_extern: *is_extern,
        function_type: infer_type_id,
        parent_set: set,
        time: ctx.runs,
        ast_variant_id: ctx.ast_variant_id,
    });

    let value_set = ctx.infer.value_sets.get_mut(sub_set);
    let old_set = value_set.emit_deps.replace(emit_deps);
    let old_target_checker = value_set.target_checker.replace(target_checker);
    debug_assert!(old_set.is_none());
    debug_assert!(old_target_checker.is_none());
}

fn build_unique_type(
    ctx: &mut Context<'_, '_>,
    node: NodeView<'_>,
    set: ValueSetId,
    marker: UniqueTypeMarker,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    match node.kind {
        NodeKind::EnumType { ref fields }=> {
            // TODO: These are ugly
            ctx.infer.set_value_set(node_type_id, set);
            ctx.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, node.id);

            let names = fields.to_vec().into_boxed_slice();
            let mut children = node.children.into_iter();
            let base_type = children.next().unwrap();
            let base_type_id = build_type(ctx, base_type, set);

            let fields: Vec<_> = std::iter::once((base_type_id, Reason::temp(node_loc))).chain(children.map(|child| {
                let value = build_inferrable_constant_value(ctx, child, set);
                ctx.infer.set_equal(value.type_, base_type_id, Reason::temp(node_loc));

                (value.constant_value, Reason::temp(node_loc))
            })).collect();

            ctx.infer.set_type(node_type_id, TypeKind::Enum(marker, names), Args(fields), set);
        }
        _ => {
            let inner_type = build_type(ctx, node, set);
            return ctx.infer.add_type(
                TypeKind::Unique(marker),
                Args([(inner_type, Reason::temp(node.loc))]),
                set,
            );
        }
    }

    node_type_id
}

fn build_type(
    ctx: &mut Context<'_, '_>,
    node: NodeView<'_>,
    set: ValueSetId,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    ctx.infer.set_value_set(node_type_id, set);
    ctx.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, node.id);

    match node.kind {
        NodeKind::IntType => {
            if ctx.inside_type_comparison {
                let inner = ctx.infer.add_type(TypeKind::CompareUnspecified, Args([]), set);
                ctx.infer.set_type(node_type_id, TypeKind::Int, Args([(inner, Reason::temp_zero()), (inner, Reason::temp_zero())]), set);
            } else {
                ctx.infer.set_type(node_type_id, TypeKind::Int, (), set);
            }
        }
        NodeKind::FloatType => {
            if ctx.inside_type_comparison {
                let inner = ctx.infer.add_type(TypeKind::CompareUnspecified, Args([]), set);
                ctx.infer.set_type(node_type_id, TypeKind::Float, Args([(inner, Reason::temp_zero())]), set);
            } else {
                ctx.infer.set_type(node_type_id, TypeKind::Float, (), set);
            }
        }
        NodeKind::ImplicitType => {
            if ctx.inside_type_comparison {
                ctx.infer.set_type(node_type_id, TypeKind::CompareUnspecified, Args([]), set);
            }
        },
        NodeKind::PolymorphicArgs => {
            let mut children = node.children.into_iter();
            let on = children.next().unwrap();
            let &NodeKind::Global { scope, name } = &on.kind else {
                todo!("Handling of the case where you pass polymorphic args to something that shouldn't have it");
            };

            ctx.infer.set_value_set(TypeId::Node(ctx.ast_variant_id, on.id), set);
            ctx.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, on.id);
            ctx.infer.set_equal(TypeId::Node(ctx.ast_variant_id, on.id), node_type_id, Reason::temp(node_loc));

            let old_runs = ctx.runs;
            ctx.runs = ExecutionTime::Never;
            let id = ctx.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");
            build_global(ctx, node.id, node.node, node.loc, id, Some(children), set, true);
            ctx.runs = old_runs;
        }
        NodeKind::Global { scope, name } => {
            let old_runs = ctx.runs;
            ctx.runs = ExecutionTime::Never;
            let id = ctx.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");
            build_global(ctx, node.id, node.node, node.loc, id, None, set, true);
            ctx.runs = old_runs;
        }
        NodeKind::PolymorphicArgument(index) => {
            let poly_param = &mut ctx.poly_params[index];
            poly_param.used_as_type.get_or_insert(node_loc);
            if poly_param.check_for_dual_purpose(ctx.errors) {
                ctx.infer.value_sets.get_mut(set).has_errors |= true;
            }
            ctx.infer.set_equal(poly_param.value_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::Parenthesis | NodeKind::TypeAsValue => {
            let [inner] = node.children.into_array();
            let inner_type_id = build_type(ctx, inner, set);
            ctx.infer
                .set_equal(inner_type_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::LiteralType(ref type_) => {
            ctx.infer.set_compiler_type(ctx.program, node_type_id, type_, set);
        }
        NodeKind::FunctionType => {
            let mut children = node.children.into_iter();
            let mut tags = build_tags(ctx, children.next().unwrap(), set);
            let mut function_args = FunctionArgsBuilder::with_num_args_capacity(children.len());
            let num_children = children.len();
            for type_node in children.by_ref().take(num_children - 1) {
                let type_id = build_type(ctx, type_node, set);
                function_args.add_arg((type_id, Reason::temp(node_loc)));
            }

            let returns_type_id = build_type(ctx, children.next().unwrap(), set);
            function_args.set_return((returns_type_id, Reason::temp(node_loc)));

            if let Some((loc, calling_convention)) = tags.calling_convention.take() {
                function_args.set_calling_convention((calling_convention, Reason::temp(loc)));
            } else {
                // TODO: This should be the borkle calling convention
                let constant_value = ctx.program.insert_buffer(&types::Type::new_int(IntTypeKind::U8), (&0_u8) as *const u8);
                let calling_convention = ctx.infer.add_type(TypeKind::ConstantValue(constant_value), Args([]), set);
                function_args.set_calling_convention((calling_convention, Reason::temp(node.loc)));
            }

            if let Some((loc, target)) = tags.target.take() {
                function_args.set_target((target, Reason::temp(loc)));
            } else {
                let constant_value = ctx.program.insert_buffer(&types::Type::new_int(IntTypeKind::U32), (&TARGET_ALL) as *const u32 as *const u8);
                let target = ctx.infer.add_type(TypeKind::ConstantValue(constant_value), Args([]), set);
                function_args.set_target((target, Reason::temp(node.loc)));
            }


            tags.finish(ctx, set);

            let infer_type_id = ctx.infer.add_type(TypeKind::Function, Args(function_args.build()), set);
            ctx.infer
                .set_equal(infer_type_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::TupleType => {
            let mut values = Vec::with_capacity(node.children.len());
            for child in node.children {
                let child_id = build_type(ctx, child, set);
                values.push((child_id, Reason::temp(node_loc)));
            }

            ctx.infer.set_type(node_type_id, TypeKind::Tuple, Args(values), set);
        }
        NodeKind::EnumType { ref fields } => {
            let names = fields.to_vec().into_boxed_slice();
            let mut children = node.children.into_iter();
            let base_type = children.next().unwrap();
            let base_type_id = build_type(ctx, base_type, set);

            let fields: Vec<_> = std::iter::once((base_type_id, Reason::temp(node_loc))).chain(children.map(|child| {
                let value = build_inferrable_constant_value(ctx, child, set);
                ctx.infer.set_equal(value.type_, base_type_id, Reason::temp(node_loc));

                (value.constant_value, Reason::temp(node_loc))
            })).collect();

            let marker = UniqueTypeMarker {
                name: None,
                loc: node_loc,
            };
            
            ctx.infer.set_type(node_type_id, TypeKind::Enum(marker, names), Args(fields), set);
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
            let length = build_inferrable_constant_value(ctx, len, set);
            let usize_type = ctx.infer.add_int(IntTypeKind::Usize, set);
            ctx.infer.set_equal(usize_type, length.type_, Reason::temp(node_loc));

            let member_type_id = build_type(ctx, members, set);
            ctx.infer.set_type(node_type_id, TypeKind::Array, Args([(member_type_id, Reason::temp(node_loc)), (length.constant, Reason::temp(node_loc))]), set);
        }
        NodeKind::TypeOf => {
            let [inner] = node.children.into_array();
            let old = ctx.runs;
            let old_inside_type_comparison = ctx.inside_type_comparison;
            ctx.inside_type_comparison = false;
            ctx.runs = ctx.runs.combine(ExecutionTime::Never);
            let type_ = build_constraints(ctx, inner, set);
            ctx.runs = old;
            ctx.inside_type_comparison = old_inside_type_comparison;
            ctx.infer.set_equal(node_type_id, type_, Reason::new(node_loc, ReasonKind::TypeOf));
        }
        NodeKind::Local { local_id } => {
            ctx.errors.info(ctx.locals.get(local_id).loc, "Defined here".to_string());
            ctx.errors.error(node_loc, "Cannot use a local as a type, did you intend to put a `typeof` before the local?".to_string());
            ctx.infer.value_sets.get_mut(set).has_errors = true;
        }
        _ => {
            ctx.errors.error(node_loc, format!("Expected a type, got {:?}", node.kind));
            ctx.infer.value_sets.get_mut(set).has_errors = true;
        }
    }

    node_type_id
}

fn build_declarative_lvalue(
    ctx: &mut Context<'_, '_>,
    node: NodeView<'_>,
    set: ValueSetId,
    is_declaring: bool,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    ctx.infer.set_value_set(node_type_id, set);
    ctx.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, node.id);

    match node.kind {
        NodeKind::Member { name } if !is_declaring => {
            let [of] = node.children.into_array();
            let of_type_id = build_lvalue(ctx, of, set, false);
            ctx.infer
                .set_field_name_equal(of_type_id, name, node_type_id, Reason::new(node_loc, ReasonKind::NamedField(name)));
        }
        NodeKind::Binary { op: BinaryOp::BitAnd } => {
            let [left, right] = node.children.into_array();

            let left_id = build_declarative_lvalue(ctx, left, set, is_declaring);
            let right_id = build_declarative_lvalue(ctx, right, set, is_declaring);

            ctx.infer.set_equal(node_type_id, left_id, Reason::temp(node_loc));
            ctx.infer.set_equal(node_type_id, right_id, Reason::temp(node_loc));
        }
        NodeKind::ImplicitType => {}
        NodeKind::Declare if !is_declaring => {
            let [inner] = node.children.into_array();
            let inner = build_declarative_lvalue(ctx, inner, set, true);
            ctx.infer.set_equal(node_type_id, inner, Reason::temp(node_loc));
        }
        NodeKind::Pack => {
            let [inner] = node.children.into_array();
            let inner_type = build_constraints(ctx, inner, set);
            ctx.infer.set_pack(node_type_id, inner_type, Reason::temp(node_loc));
        }
        NodeKind::Unpack => {
            let [inner] = node.children.into_array();
            let inner_type = build_constraints(ctx, inner, set);
            ctx.infer.set_pack(inner_type, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::Local{ local_id } => {
            if is_declaring {
                let local = ctx.locals.get_mut(local_id);
                local.declared_at = Some(node.id);
                local.stack_frame_id = set;
                // Usage doesn't need to be set, because this is a declaration, and therefore mutability of the
                // variable doesn't matter yet.
            } else {
                let local = ctx.locals.get(local_id);
                let local_type_id = TypeId::Node(ctx.ast_variant_id, local.declared_at.unwrap());
                ctx.infer
                    .set_equal(local_type_id, node_type_id, Reason::new(node_loc, ReasonKind::LocalVariableIs(local.name)));
                if local.stack_frame_id != set {
                    ctx.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type".to_string());
                    ctx.infer.value_sets.get_mut(set).has_errors = true;
                }
            }
        }
        NodeKind::Parenthesis => {
            let [value] = node.children.into_array();
            let inner = build_declarative_lvalue(ctx, value, set, is_declaring);
            ctx.infer.set_equal(node_type_id, inner, Reason::temp(node_loc));
        }
        NodeKind::Tuple => {
            let mut values = Vec::with_capacity(node.children.len());
            for child in node.children {
                let child_id = build_declarative_lvalue(ctx, child, set, is_declaring);
                values.push((child_id, Reason::temp(node_loc)));
            }

            ctx.infer.set_type(node_type_id, TypeKind::Tuple, Args(values), set);
        }
        NodeKind::ArrayLiteral => {
            let inner_type = ctx.infer.add_unknown_type_with_set(set);

            for arg in node.children.into_iter() {
                let arg_type_id = build_declarative_lvalue(ctx, arg, set, is_declaring);
                ctx.infer.set_equal(arg_type_id, inner_type, Reason::new(node_loc, ReasonKind::Passed));
            }

            let usize = ctx.infer.add_int(IntTypeKind::Usize, set);
            let length = ctx.program.insert_buffer(&types::Type::new_int(IntTypeKind::Usize), (node.children.len()).to_le_bytes().as_ptr());

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
            let value_type_id = build_declarative_lvalue(ctx, value, set, is_declaring);
            ctx.infer
                .set_equal(value_type_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } if !is_declaring => {
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
            ctx.errors.error(node_loc, "Not a valid declarative lvalue".to_string());
            ctx.infer.value_sets.get_mut(set).has_errors = true;
        }
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
    node: NodeView<'_>,
    set: ValueSetId,
    can_reference_temporaries: bool,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    match node.kind {
        NodeKind::Member { name } => {
            let [of] = node.children.into_array();
            let of_type_id = build_lvalue(ctx, of, set, can_reference_temporaries);
            ctx.infer
                .set_field_name_equal(of_type_id, name, node_type_id, Reason::new(node_loc, ReasonKind::NamedField(name)));
        }
        NodeKind::Local { local_id } => {
            let local = ctx.locals.get(local_id);
            
            let local_type_id = TypeId::Node(ctx.ast_variant_id, local.declared_at.unwrap());
            ctx.infer
                .set_equal(local_type_id, node_type_id, Reason::new(node_loc, ReasonKind::LocalVariableIs(local.name)));

            if local.stack_frame_id != set {
                ctx.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type".to_string());
                ctx.infer.value_sets.get_mut(set).has_errors = true;
            }
        }
        NodeKind::Parenthesis => {
            let [value] = node.children.into_array();
            let inner = build_lvalue(ctx, value, set, can_reference_temporaries);
            ctx.infer.set_equal(node_type_id, inner, Reason::temp(node_loc));
        }
        NodeKind::Pack => {
            let [inner] = node.children.into_array();
            let inner_type = build_constraints(ctx, inner, set);
            ctx.infer.set_pack(node_type_id, inner_type, Reason::temp(node_loc));
        }
        NodeKind::Unpack => {
            let [inner] = node.children.into_array();
            let inner_type = build_constraints(ctx, inner, set);
            ctx.infer.set_pack(inner_type, node_type_id, Reason::temp(node_loc));
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
            let value_type_id = build_lvalue(ctx, value, set, can_reference_temporaries);
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
            if can_reference_temporaries {
                // Make it a reference to a temporary instead. This forces the pointer to be readonly.
                // TODO: Make it require it to be read-only here.
                return build_constraints(ctx, node, set);
            } else {
                ctx.errors.error(node_loc, "Not a valid lvalue, as this is assigned to, we can't use temporary values".to_string());
                ctx.infer.value_sets.get_mut(set).has_errors = true;
            }
        }
    }

    ctx.infer.set_value_set(node_type_id, set);
    ctx.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, node.id);

    node_type_id
}

struct TypeSystemConstant {
    type_: TypeId,
    constant: TypeId,
    constant_value: TypeId,
}

// The first return is the type of the constant, the second return is the value id of that constant, where the constant will later be stored.
fn build_inferrable_constant_value(
    ctx: &mut Context<'_, '_>,
    node: NodeView<'_>,
    set: ValueSetId,
) -> TypeSystemConstant {
    let node_loc = node.loc;
    let node_id = node.id;
    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    let type_system_constant = match node.kind {
        NodeKind::PolymorphicArgument(index) => {
            let constant_value = ctx.infer.add_unknown_type_with_set(set);
            let constant = ctx.infer.add_type(TypeKind::Constant, Args([(node_type_id, Reason::temp(node_loc)), (constant_value, Reason::temp(node_loc))]), set);
            let poly_param = &mut ctx.poly_params[index];
            poly_param.used_as_value.get_or_insert(node_loc);
            if poly_param.check_for_dual_purpose(ctx.errors) {
                ctx.infer.value_sets.get_mut(set).has_errors |= true;
            }
            ctx.infer.set_equal(poly_param.value_id, constant, Reason::temp(node_loc));
            
            TypeSystemConstant { type_: node_type_id, constant, constant_value }
        }
        NodeKind::ImplicitType => {
            if ctx.inside_type_comparison {
                let unspecified = ctx.infer.add_type(TypeKind::CompareUnspecified, Args([]), set);
                let constant = ctx.infer.add_type(TypeKind::Constant, Args([(node_type_id, Reason::temp(node_loc)), (unspecified, Reason::temp(node_loc))]), set);

                TypeSystemConstant { type_: node_type_id, constant_value: unspecified, constant }
            } else {
                // Nothing at all is known about it, _except_ that the type of this node is equal to the
                // value.
                let constant_value = ctx.infer.add_unknown_type_with_set(set);
                let constant = ctx.infer.add_type(TypeKind::Constant, Args([(node_type_id, Reason::temp(node_loc)), (constant_value, Reason::temp(node_loc))]), set);
                TypeSystemConstant { type_: node_type_id, constant_value, constant }
            }
        }
        _ => {
            // We can't figure it out in a clever way, so just compile time execute the node as a constant.
            let mut sub_ctx = Context {
                thread_context: ctx.thread_context,
                errors: ctx.errors,
                program: ctx.program,
                locals: ctx.locals,
                // TODO: Think about whether this is correct or not
                emit_deps: ctx.emit_deps,
                poly_params: ctx.poly_params,
                infer: ctx.infer,
                runs: ctx.runs.combine(ExecutionTime::Typing),
                needs_explaining: ctx.needs_explaining,
                ast_variant_id: ctx.ast_variant_id,
                additional_info: ctx.additional_info,
                inside_type_comparison: false,
                // TODO: We don't ever use this thing....
                target_checker: TargetChecker::default(),
            };
            let sub_set = sub_ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);

            let constant_type_id = build_constraints(&mut sub_ctx, node, sub_set);
            let constant_value = ctx.infer.add_unknown_type_with_set(set);
            let value_id = ctx.infer.add_type(TypeKind::Constant, Args([(constant_type_id, Reason::temp(node_loc)), (constant_value, Reason::temp(node_loc))]), set);
            ctx.infer.set_equal(node_type_id, constant_type_id, Reason::temp(node_loc));

            ctx.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::ValueIdFromConstantComputation {
                computation: node_id,
                value_id,
                ast_variant_id: ctx.ast_variant_id,
            });

            // Because the set of the node is already set by build_constraints, we early return type
            return TypeSystemConstant { type_: node_type_id, constant_value, constant: value_id };
        }
    };

    ctx.infer.set_value_set(node_type_id, set);
    ctx.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, node_id);

    type_system_constant
}

fn build_with_metadata(
    ctx: &mut Context<'_, '_>,
    node: NodeView<'_>,
    set: ValueSetId,
) -> Option<Arc<MemberMetaData>> {
    match node.kind {
        NodeKind::PolymorphicArgs => {
            let node_loc = node.loc;
            let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

            let mut children = node.children.into_iter();
            let on = children.next().unwrap();
            let &NodeKind::Global { scope, name } = &on.kind else {
                todo!("Handling of the case where you pass polymorphic args to something that shouldn't have it");
            };

            ctx.infer.set_value_set(TypeId::Node(ctx.ast_variant_id, on.id), set);
            ctx.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, on.id);
            ctx.infer.set_equal(TypeId::Node(ctx.ast_variant_id, on.id), node_type_id, Reason::temp(node_loc));

            let id = ctx.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");
            Some(build_global(ctx, node.id, node.node, node.loc, id, Some(children), set, false))
        }
        NodeKind::Global { scope, name } => {
            let id = ctx.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");
            Some(build_global(ctx, node.id, node.node, node.loc, id, None, set, false))
        }
        _ => {
            build_constraints(ctx, node, set);
            None
        }
    }
}

fn build_function_call<'a>(
    ctx: &mut Context<'_, '_>,
    node_id: NodeId,
    node_type_id: TypeId,
    node_loc: Location,
    calling_type_id: TypeId,
    meta_data: Option<Arc<MemberMetaData>>,
    children: impl Iterator<Item = NodeView<'a>> + Clone + 'a,
    set: ValueSetId,
) {
    if let Some(MemberMetaData::Function(FunctionMetaData { arguments })) = meta_data.as_deref() {
        #[derive(Clone)]
        enum ArgDefinedAs {
            None,
            Literal(Location, TypeId),
            VarArgs(Location, Vec<(TypeId, Reason)>),
        }

        let mut arg_defined = vec![ArgDefinedAs::None; arguments.len()];
        let mut function_arg_usage = Vec::with_capacity(children.size_hint().0);
        let mut anonymous_index = 0;
        for mut arg in children.clone() {
            let name = match arg.kind {
                NodeKind::Binary { op: BinaryOp::Assign, .. } => {
                    let [left, right] = arg.children.into_array();

                    if let NodeKind::AnonymousMember { name } = left.kind {
                        arg = right;
                        Some((left.loc, name))
                    } else {
                        None
                    }
                }
                _ => None,
            };

            let index = match name {
                Some((name_loc, name)) => {
                    match arguments.iter().position(|v| v.name.map(|v| v.0) == Some(name)) {
                        Some(index) => index,
                        None => {
                            ctx.errors.error(name_loc, format!("Invalid argument name, `{}`", name));
                            ctx.infer.value_sets.get_mut(set).has_errors |= true;
                            continue;
                        }
                    }
                }
                None => {
                    anonymous_index
                }
            };

            let arg_id = build_constraints(ctx, arg, set);

            let Some(arg_info) = arguments.get(index) else {
                ctx.errors.error(arg.loc, "Too many arguments passed to function".to_string());
                ctx.infer.value_sets.get_mut(set).has_errors |= true;
                break;
            };

            let arg_defined_as = &mut arg_defined[index];
            match *arg_info {
                FunctionArgumentInfo { var_args: Some(var_args_loc), .. } if name.is_none() => {
                    match *arg_defined_as {
                        ArgDefinedAs::None => {
                            *arg_defined_as = ArgDefinedAs::VarArgs(arg.loc, vec![(arg_id, Reason::temp(arg.loc))]);
                            function_arg_usage.push(FunctionArgUsage::TupleElement { function_arg: index, field: 0 });
                        }
                        ArgDefinedAs::Literal(prev_loc, _) => {
                            ctx.errors.info(var_args_loc, "Defined as a var_arg here".to_string());
                            ctx.errors.info(prev_loc, "Assigned literally here".to_string());
                            ctx.errors.error(arg.loc, "Cannot pass something both as a var_arg and as a literal value at once".to_string());
                            ctx.infer.value_sets.get_mut(set).has_errors |= true;
                            return;
                        }
                        ArgDefinedAs::VarArgs(_, ref mut usages) => {
                            function_arg_usage.push(FunctionArgUsage::TupleElement { function_arg: index, field: usages.len() });
                            usages.push((arg_id, Reason::temp(arg.loc)));
                        }
                    }
                }
                _ => {
                    match *arg_defined_as {
                        ArgDefinedAs::None => {
                            *arg_defined_as = ArgDefinedAs::Literal(arg.loc, arg_id);
                            if name.is_some() {
                                function_arg_usage.push(FunctionArgUsage::ValueOfAssign { function_arg: index });
                            } else {
                                function_arg_usage.push(FunctionArgUsage::Value { function_arg: index });
                            }
                        }
                        ArgDefinedAs::Literal(prev_loc, _) | ArgDefinedAs::VarArgs(prev_loc, _) => {
                            ctx.errors.info(prev_loc, "Previously defined here".to_string());
                            ctx.errors.error(arg.loc, "Argument defined twice".to_string());
                            ctx.infer.value_sets.get_mut(set).has_errors |= true;
                            return;
                        }
                    }

                    if name.is_none() {
                        anonymous_index += 1;
                    }
                }
            }
        }

        let mut typer_args = FunctionArgsBuilder::with_num_args_capacity(children.size_hint().0);
        typer_args.set_return((node_type_id, Reason::new(node_loc, ReasonKind::FunctionCallReturn)));

        for (i, (defined, defined_arg)) in arg_defined.into_iter().zip(arguments).enumerate() {
            match defined {
                ArgDefinedAs::None => {
                    if defined_arg.var_args.is_some() {
                        let tuple_type = ctx.infer.add_type(TypeKind::Tuple, Args([]), set);
                        typer_args.add_arg((tuple_type, Reason::temp(node_loc)));
                    } else {
                        ctx.errors.error(node_loc, format!("Argument `{}` not defined", i));
                        return;
                    }
                }
                ArgDefinedAs::Literal(node_loc, type_id) => {
                    typer_args.add_arg((type_id, Reason::temp(node_loc)));
                }
                ArgDefinedAs::VarArgs(node_loc, type_id) => {
                    let tuple_type = ctx.infer.add_type(TypeKind::Tuple, Args(type_id), set);
                    typer_args.add_arg((tuple_type, Reason::temp(node_loc)));
                }
            }
        }

        let calling_convention = ctx.infer.add_unknown_type_with_set(set);
        typer_args.set_calling_convention((calling_convention, Reason::temp(node_loc)));

        let target = ctx.infer.add_unknown_type_with_set(set);
        typer_args.set_target((target, Reason::temp(node_loc)));

        if let Some(&parent) = ctx.target_checker.stack.last() {
            ctx.target_checker.checks.push(TargetCheck {
                loc: node_loc,
                subset: parent,
                superset: target,
            });
        }

        // Specify that the caller has to be a function type
        let type_id = ctx.infer.add_type(TypeKind::Function, Args(typer_args.build()), set);
        ctx.additional_info.insert((ctx.ast_variant_id, node_id), AdditionalInfoKind::FunctionCall(function_arg_usage));
        ctx.infer
            .set_equal(calling_type_id, type_id, Reason::new(node_loc, ReasonKind::FunctionCall));
    } else {
        let mut typer_args = FunctionArgsBuilder::with_num_args_capacity(children.size_hint().0);

        for arg in children {
            let arg_type_id = build_constraints(ctx, arg, set);
            typer_args.add_arg((arg_type_id, Reason::new(node_loc, ReasonKind::FunctionCallArgument)));
        }

        let calling_convention = ctx.infer.add_unknown_type_with_set(set);
        typer_args.set_calling_convention((calling_convention, Reason::temp(node_loc)));
        typer_args.set_return((node_type_id, Reason::new(node_loc, ReasonKind::FunctionCallReturn)));

        let target = ctx.infer.add_unknown_type_with_set(set);
        typer_args.set_target((target, Reason::temp(node_loc)));

        if let Some(&parent) = ctx.target_checker.stack.last() {
            ctx.target_checker.checks.push(TargetCheck {
                loc: node_loc,
                subset: parent,
                superset: target,
            });
        }

        // Specify that the caller has to be a function type
        let type_id = ctx.infer.add_type(TypeKind::Function, Args(typer_args.build()), set);
        ctx.infer
            .set_equal(calling_type_id, type_id, Reason::new(node_loc, ReasonKind::FunctionCall));
    }
}

fn build_global<'a>(
    ctx: &mut Context<'_, '_>,
    node_id: NodeId,
    // TODO: Why are all of these separate instead of just NodeView?
    node: &Node,
    node_loc: Location,
    id: PolyOrMember,
    children: Option<GenericChildIterator<'a, &'a [Node]>>,
    set: ValueSetId,
    expecting_type: bool,
) -> Arc<MemberMetaData> {
    debug_assert!(!(ctx.inside_type_comparison && !expecting_type));

    let node_type_id = TypeId::Node(ctx.ast_variant_id, node_id);

    let (meta_data, member_kind) = ctx.program.get_member_meta_data_and_kind(id);

    if matches!(member_kind, MemberKind::Type { .. }) != expecting_type {
        match member_kind {
            MemberKind::Const => {
                ctx.errors.error(node.loc, format!("Cannot use `const` values in a type expression, did you intend to add a `typeof` in front?"));
            }
            MemberKind::Type { .. } => {
                ctx.errors.error(node.loc, format!("Cannot use `type` values as expressions, they are only allowed in types."));
            }
        }
        ctx.infer.value_sets.get_mut(set).has_errors |= true;
    }

    match id {
        PolyOrMember::Poly(id) => {
            let num_args = ctx.program.get_num_poly_args(id);
            let other_yield_data = ctx.program.get_polymember_yielddata(id);

            let mut param_values = Vec::with_capacity(num_args);
            let mut param_reasons = Vec::with_capacity(num_args);
            let sub_set = ctx.infer.value_sets.add(WaitingOnTypeInferrence::None);

            if let Some(children) = children {
                if num_args != children.len() {
                    ctx.errors.error(node_loc, format!("Passed {} arguments to polymorphic value, but the polymorphic value needs {} values", children.len(), num_args));
                    // @Cleanup: This should probably just be a function on TypeSystem
                    ctx.infer.value_sets.get_mut(set).has_errors |= true;
                    return meta_data;
                }

                for (i, (param, other_poly_arg)) in children.zip(&other_yield_data.poly_params).enumerate() {
                    let param_loc = param.loc;
                    if other_poly_arg.is_type() {
                        let type_id = build_type(ctx, param, sub_set);
                        param_values.push(type_id);
                        param_reasons.push((type_id, other_poly_arg.value_id, Reason::new(param_loc, ReasonKind::PolyParam(i))));
                    } else {
                        let param_value = build_inferrable_constant_value(ctx, param, sub_set);
                        param_values.push(param_value.constant);
                        param_reasons.push((param_value.constant, other_poly_arg.value_id, Reason::new(param_loc, ReasonKind::PolyParam(i))));
                    }
                }
            } else {
                for (i, other_poly_arg) in other_yield_data.poly_params.iter().enumerate() {
                    if ctx.inside_type_comparison {
                        // @Copypasta
                        if other_poly_arg.is_type() {
                            let type_id = ctx.infer.add_type(TypeKind::CompareUnspecified, Args([]), sub_set);
                            param_values.push(type_id);
                            param_reasons.push((type_id, other_poly_arg.value_id, Reason::new(node_loc, ReasonKind::PolyParam(i))));
                        } else {
                            let unknown = ctx.infer.add_unknown_type_with_set(sub_set);
                            let unspecified = ctx.infer.add_type(TypeKind::CompareUnspecified, Args([]), sub_set);
                            let type_id = ctx.infer.add_type(TypeKind::Constant, Args([(unknown, Reason::temp(node_loc)), (unspecified, Reason::temp(node_loc))]), sub_set);
                            param_values.push(type_id);
                            param_reasons.push((type_id, other_poly_arg.value_id, Reason::new(node_loc, ReasonKind::PolyParam(i))));
                        }
                    } else {
                        let type_id = ctx.infer.add_unknown_type_with_set(sub_set);
                        param_values.push(type_id);
                        param_reasons.push((type_id, other_poly_arg.value_id, Reason::new(node.loc, ReasonKind::PolyParam(i))));
                    }
                }
            }

            param_reasons.push((node_type_id, other_yield_data.root_value_id, Reason::new(node.loc, ReasonKind::PolyMember(id))));

            let poly_loc = ctx.program.get_polymember_loc(id);

            ctx.infer.add_subtree_from_other_typesystem(
                &other_yield_data.infer, 
                param_reasons.into_iter(),
                poly_loc,
            );

            ctx.infer.value_sets.lock(set);

            if !ctx.inside_type_comparison {
                ctx.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::MonomorphiseMember {
                    node_id: node_id,
                    poly_member_id: id,
                    when_needed: ctx.runs,
                    params: param_values,
                    parent_set: set,
                    ast_variant_id: ctx.ast_variant_id,
                });
            }
        }
        PolyOrMember::Member(id) => {
            if children.map_or(0, |v| v.len()) > 0 {
                // This is an error, since it's not polymorphic
                ctx.errors.error(node.loc, "Passed polymorphic parameters even though this value isn't polymorphic".to_string());
                // @Cleanup: This should probably just be a function on TypeSystem
                ctx.infer.value_sets.get_mut(set).has_errors |= true;
                return meta_data;
            }

            let type_ = ctx.program.get_member_type(id);

            let type_id = ctx.infer.add_compiler_type(
                ctx.program,
                &type_,
                set,
            );

            ctx.infer.set_equal(node_type_id, type_id, Reason::new(node.loc, ReasonKind::IsOfType));

            match ctx.runs {
                // This will never be emitted anyway so it doesn't matter if the value isn't accessible.
                ExecutionTime::Never => {},
                ExecutionTime::RuntimeFunc => {
                    ctx.emit_deps.add(node.loc, DepKind::Member(id, MemberDep::Value));
                }
                ExecutionTime::Emission => {
                    ctx.emit_deps.add(node.loc, DepKind::Member(id, MemberDep::ValueAndCallableIfFunction));
                }
                ExecutionTime::Typing => {
                    // The parser should have already made sure the value is accessible. We will run this node
                    // through the emitter anyway though, so we don't have to make it into a constant or something.
                }
            }

            ctx.additional_info.insert((ctx.ast_variant_id, node_id), AdditionalInfoKind::Monomorphised(id));
        }
    }

    meta_data
}

#[derive(Clone)]
pub enum WaitingOnTypeInferrence {
    ConditionalCompilation {
        node_id: NodeId,
        condition: NodeId,
        true_body: NodeId,
        false_body: NodeId,
        ast_variant_id: AstVariantId,
        runs: ExecutionTime,
        parent_set: ValueSetId,
    },
    ConstFor {
        node_id: NodeId,
        ast_variant_id: AstVariantId,
        runs: ExecutionTime,
        iterator_type: TypeId,
        parent_set: ValueSetId,
    },
    SizeOf {
        parent_set: ValueSetId,
    },
    MonomorphiseMember {
        node_id: NodeId,
        poly_member_id: PolyMemberId,
        when_needed: ExecutionTime,
        params: Vec<type_infer::ValueId>,
        parent_set: ValueSetId,
        ast_variant_id: AstVariantId,
    },
    FunctionDeclaration {
        node_id: NodeId,
        is_extern: Option<Ustr>,
        function_type: TypeId,
        /// This is because function declaration create a constant in the
        /// parent set, and we have to make sure that the parent set isn't
        /// emitted before that constant is created.
        parent_set: ValueSetId,
        time: ExecutionTime,
        ast_variant_id: AstVariantId,
    },
    BuiltinFunctionInTyping {
        node_id: NodeId,
        function: BuiltinFunction,
        parent_set: ValueSetId,
        ast_variant_id: AstVariantId,
    },
    ConstantFromValueId {
        value_id: type_infer::ValueId,
        to: NodeId,
        parent_set: ValueSetId,
        ast_variant_id: AstVariantId,
    },
    ValueIdFromConstantComputation {
        computation: NodeId,
        ast_variant_id: AstVariantId,
        value_id: type_infer::ValueId,
    },
    None,
}
