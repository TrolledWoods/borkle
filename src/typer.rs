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
    target_checks: Vec<TargetCheck>,
}

impl YieldData {
    pub fn insert_poly_params(&mut self, program: &Program, poly_args: &[crate::types::Type]) {
        for (param, compiler_type) in self.poly_params.iter().zip(poly_args) {
            if param.is_type() {
                let type_id = self.infer.add_compiler_type(program, compiler_type);
                self.infer.set_equal(param.value_id, type_id, Reason::temp_zero());
            } else {
                let constant = self.infer.add_compiler_type(program, compiler_type);
                self.infer.set_equal(constant, param.value_id, Reason::temp_zero());
            }
        }
    }
}

/// Things that are global across the whole typer, independant of value sets, and other garbage like that.
struct Statics<'a, 'b> {
    thread_context: &'a mut ThreadContext<'b>,
    errors: &'a mut ErrorCtx,
    program: &'b Program,
    locals: &'a mut LocalVariables,
    infer: &'a mut TypeSystem,
    needs_explaining: &'a mut Vec<(NodeId, type_infer::ValueId)>,
    poly_params: &'a mut Vec<PolyParam>,
    additional_info: &'a mut AdditionalInfo,

    // TODO: this should really be moved to `AstVariantContext`, I made a mistake putting it here....
    // Since we probably want to check this before we compute any value set... why are value sets and ast variants separate again?
    target_checks: &'a mut Vec<TargetCheck>,
}

/// Things that each ast variant has. 
// TODO: I don't really want default to be implemented for this.
#[derive(Default, Clone)]
pub struct AstVariantContext {
    /// Dependencies necessary for being able to emit code for this output.
    emit_deps: DependencyList,
}

#[derive(Clone)]
struct Context {
    runs: ExecutionTime,
    inside_type_comparison: bool,
    ast_variant_id: AstVariantId,
    target: Option<TypeId>,
}

#[derive(Clone)]
struct TargetCheck {
    loc: Location,
    subset: TypeId,
    superset: TypeId,
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
    let mut target_checks = Vec::new();

    let mut statics = Statics {
        thread_context,
        errors,
        program,
        locals: &mut locals,
        infer: &mut infer,
        needs_explaining: &mut needs_explaining,
        poly_params: &mut poly_params,
        additional_info: &mut additional_info,
        target_checks: &mut target_checks,
    };

    let mut ast_variant_ctx = AstVariantContext {
        emit_deps: DependencyList::new(),
    };

    let mut ctx = Context {
        runs: ExecutionTime::RuntimeFunc,
        ast_variant_id: AstVariantId::root(),
        inside_type_comparison: false,
        target: None,
    };

    // Build the type relationships between nodes.
    let root_set_id = statics.infer.value_sets.add(WaitingOnTypeInferrence::None);

    let node = ast.root();
    let (root_value_id, meta_data) = match node.kind {
        NodeKind::FunctionDeclaration { .. } => {
            let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);
            statics.infer.set_value_set(node_type_id, root_set_id);
            statics.infer.value_sets.add_node_to_set(root_set_id, ctx.ast_variant_id, node.id);
            let mut meta_data = FunctionMetaData::default();
            build_function_declaration(&mut statics, &mut ast_variant_ctx, &mut ctx, node, root_set_id, Some(&mut meta_data));

            (node_type_id, MemberMetaData::Function(meta_data))
        }
        _ => (
            match member_kind {
                MemberKind::Type { is_aliased: false } => {
                    build_unique_type(&mut statics, &mut ast_variant_ctx,  &mut ctx, node, root_set_id, UniqueTypeMarker { name: Some(ast.name), loc: node.loc })
                }
                MemberKind::Type { is_aliased: true } => {
                    build_type(&mut statics, &mut ast_variant_ctx, &mut ctx, node, root_set_id)
                }
                MemberKind::Const => {
                    build_constraints(&mut statics, &mut ast_variant_ctx,  &mut ctx, node, root_set_id)
                }
            },
            MemberMetaData::None,
        )
    };

    let value_set = infer.value_sets.get_mut(root_set_id);
    value_set.ctx = Some(ast_variant_ctx);

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
            target_checks,
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
    let mut target_checks = Vec::new();
    let mut statics = Statics {
        thread_context,
        errors,
        program,
        locals: &mut data.locals,
        infer: &mut data.infer,
        needs_explaining: &mut data.needs_explaining,
        poly_params: &mut data.poly_params,
        additional_info: &mut data.additional_info,
        target_checks: &mut target_checks,
    };

    loop {
        statics.infer.solve();

        let mut progress = false;
        for value_set_id in statics.infer.value_sets.iter_ids() {
            let value_set = statics.infer.value_sets.get_mut(value_set_id);
            if value_set.has_errors
            || value_set.has_been_computed
            || value_set.uncomputed_values() > 0
            {
                continue;
            }

            debug_assert_eq!(value_set.uncomputed_values(), 0, "The number of uncomputed values cannot be less than zero");

            let related_nodes = std::mem::take(&mut value_set.related_nodes);

            let value_set = statics.infer.value_sets.get_mut(value_set_id);
            value_set.related_nodes = related_nodes;
            value_set.has_been_computed = true;
            let waiting_on = std::mem::replace(&mut value_set.waiting_on_completion, WaitingOnTypeInferrence::None);

            let has_errors = value_set.has_errors;
            if !has_errors {
                subset_was_completed(&mut statics, &mut data.ast, waiting_on, value_set_id);
            }

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

    let ast_variant_ctx = from.infer.value_sets.get_mut(from.root_set_id).ctx.take().unwrap();

    Ok(Ok((ast_variant_ctx.emit_deps, from.locals, from.infer, from.ast, from.root_value_id, from.additional_info)))
}

fn subset_was_completed(statics: &mut Statics<'_, '_>, ast: &mut Ast, waiting_on: WaitingOnTypeInferrence, set: ValueSetId) {
    match waiting_on {
        WaitingOnTypeInferrence::TargetFromConstantValue { value_id, computation, ast_variant_id } => {
            let len_loc = ast.get(computation).loc;
            match crate::interp::emit_and_run(
                statics.thread_context,
                statics.program,
                statics.locals,
                statics.infer,
                ast,
                statics.additional_info,
                computation,
                ast_variant_id,
                &mut vec![len_loc],
            ) {
                Ok(constant_ref) => {
                    let computation_node = ast.get(computation);

                    let number = unsafe { *constant_ref.as_ptr().cast::<u32>() };
                    let finished_value = statics.infer.add_type(TypeKind::Target { min: number, max: number }, Args([]));
                    statics.infer.set_equal(finished_value, value_id, Reason::new(computation_node.loc, ReasonKind::IsOfType));
                }
                Err((message, call_stack)) => {
                    for &caller in call_stack.iter().rev().skip(1) {
                        statics.errors.info(caller, "".to_string());
                    }

                    statics.errors.error(*call_stack.last().unwrap(), message);
                    statics.infer.value_sets.get_mut(set).has_errors = true;
                }
            }
        }
        WaitingOnTypeInferrence::ConstFor { node_id, ast_variant_id, parent_set, runs, iterator_type } => {
            let node = ast.get(node_id);
            let [iterator, _i_value, mut inner, _else_body] = node.children.into_array();

            let mut iterator_type = statics.infer.get(iterator_type);

            let mut referenced = false;
            if matches!(iterator_type.kind(), TypeKind::Reference) {
                iterator_type = statics.infer.get(iterator_type.args()[0]);
                referenced = true;
            }

            if !matches!(iterator_type.kind(), TypeKind::Tuple) {
                statics.errors.error(iterator.loc, "Constant for loops can only iterate over tuples or references of tuples".to_string());
                return;
            }

            let iterator_args: Vec<_> = if referenced {
                iterator_type.args().to_vec().into_iter().map(|v| {
                    let value = statics.infer.add_type(TypeKind::Reference, Args([(v, Reason::temp(node.loc))]));
                    // TODO: Is this necessary?
                    statics.infer.set_value_set(value, parent_set);
                    value
                }).collect()
            } else {
                iterator_type.args().to_vec()
            };

            let mut sub_ast_variant_ctx = statics.infer.value_sets.get_mut(parent_set).ctx.take().unwrap_or_default();

            let mut sub_ctx = Context {
                runs,
                ast_variant_id: AstVariantId::invalid(),
                inside_type_comparison: false,
                // TODO: This is incorrect, we're going to change things up a lot later.
                target: None,
            };

            let mut variant_ids = Vec::with_capacity(iterator_args.len());
            for iterator_arg in iterator_args {
                let sub_variant_id = statics.infer.values.add_ast_variant(ast_variant_id, inner.subtree_region());
                sub_ctx.ast_variant_id = sub_variant_id;
                variant_ids.push(sub_variant_id);

                let [v_value_decl, body] = inner.children.borrow().into_array();

                let v_value_id = build_declarative_lvalue(statics, &mut sub_ast_variant_ctx, &mut sub_ctx, v_value_decl, parent_set, true);
                statics.infer.set_equal(iterator_arg, v_value_id, Reason::temp(node.node.loc));

                build_constraints(statics, &mut sub_ast_variant_ctx, &mut sub_ctx, body, parent_set);
            }

            statics.infer.value_sets.get_mut(parent_set).ctx = Some(sub_ast_variant_ctx);
            statics.additional_info.insert((ast_variant_id, node_id), AdditionalInfoKind::ConstForAstVariants { referenced, variant_ids });

            statics.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::ConditionalCompilation { node_id, condition, true_body, false_body, ast_variant_id, parent_set, runs } => {
            let loc = ast.get(condition).loc;
            let result = match crate::interp::emit_and_run(
                statics.thread_context,
                statics.program,
                statics.locals,
                statics.infer,
                ast,
                statics.additional_info,
                condition,
                ast_variant_id,
                &mut vec![loc],
            ) {
                Ok(constant_ref) => {
                    unsafe { *constant_ref.as_ptr().cast::<u8>() > 0 }
                }
                Err((message, call_stack)) => {
                    for &caller in call_stack.iter().rev().skip(1) {
                        statics.errors.info(caller, "".to_string());
                    }

                    statics.errors.error(*call_stack.last().unwrap(), message);
                    statics.infer.value_sets.get_mut(set).has_errors = true;

                    return;
                }
            };
            
            let emitting = if result { true_body } else { false_body };

            let mut sub_ast_variant_ctx = statics.infer.value_sets.get_mut(parent_set).ctx.take().unwrap_or_default();

            let mut sub_ctx = Context {
                runs,
                ast_variant_id,
                inside_type_comparison: false,
                // TODO: This is not correct...
                target: None,
            };

            let child_type = build_constraints(statics, &mut sub_ast_variant_ctx, &mut sub_ctx, ast.get(emitting), parent_set);
            statics.infer.value_sets.get_mut(parent_set).ctx = Some(sub_ast_variant_ctx);
            statics.infer.set_equal(TypeId::Node(ast_variant_id, node_id), child_type, Reason::temp_zero());

            statics.additional_info.insert((ast_variant_id, node_id), AdditionalInfoKind::ConstIfResult(result));
            statics.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::ConstantFromValueId { value_id, to, ast_variant_id, parent_set } => {
            // We expect the type to already be checked by some other mechanism,
            // e.g., node_type_id should be equal to the type of the constant.
            let constant_ref = statics.infer.extract_constant_temp(value_id).unwrap();

            statics.additional_info.insert((ast_variant_id, to), AdditionalInfoKind::Constant(constant_ref));
            statics.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::SizeOf { parent_set } => {
            statics.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::MonomorphiseMember { node_id, poly_member_id, when_needed, params, parent_set, ast_variant_id } => {
            let node_loc = ast.get(node_id).loc;
            let mut fixed_up_params = Vec::with_capacity(params.len());

            for param in params {
                fixed_up_params.push(statics.infer.value_to_compiler_type(param));
            }

            let wanted_dep = match when_needed {
                ExecutionTime::Typing => MemberDep::ValueAndCallableIfFunction,
                _ => MemberDep::Type,
            };

            statics.infer.value_sets.unlock(parent_set);

            if let Ok(member_id) = statics.program.monomorphise_poly_member(statics.errors, statics.thread_context, poly_member_id, &fixed_up_params, wanted_dep) {
                let type_ = statics.program.get_member_type(member_id);

                let compiler_type = statics.infer.add_compiler_type(statics.program, &type_);
                statics.infer.set_equal(TypeId::Node(ast_variant_id, node_id), compiler_type, Reason::new(node_loc, ReasonKind::IsOfType));

                statics.additional_info.insert((ast_variant_id, node_id), AdditionalInfoKind::Monomorphised(member_id));

                match when_needed {
                    // This will never be emitted anyway so it doesn't matter if the value isn't accessible.
                    ExecutionTime::Never => {},
                    ExecutionTime::RuntimeFunc => {
                        let sub_ast_variant_ctx = statics.infer.value_sets.get_mut(parent_set).ctx.as_mut().unwrap();
                        sub_ast_variant_ctx.emit_deps.add(node_loc, DepKind::Member(member_id, MemberDep::Value));
                    }
                    ExecutionTime::Emission => {
                        let sub_ast_variant_ctx = statics.infer.value_sets.get_mut(parent_set).ctx.as_mut().unwrap();
                        sub_ast_variant_ctx.emit_deps.add(node_loc, DepKind::Member(member_id, MemberDep::ValueAndCallableIfFunction));
                    }
                    ExecutionTime::Typing => {
                        // The parser should have already made sure the value is accessible. We will run this node
                        // through the emitter anyway though, so we don't have to make it into a constant or something.
                    }
                }
            } else {
                statics.infer.value_sets.get_mut(parent_set).has_errors |= true;
            }
        }
        WaitingOnTypeInferrence::ValueIdFromConstantComputation { computation, value_id, ast_variant_id } => {
            let len_loc = ast.get(computation).loc;
            match crate::interp::emit_and_run(
                statics.thread_context,
                statics.program,
                statics.locals,
                statics.infer,
                ast,
                statics.additional_info,
                computation,
                ast_variant_id,
                &mut vec![len_loc],
            ) {
                Ok(constant_ref) => {
                    let computation_node = ast.get(computation);
                    let finished_value = statics.infer.add_value(TypeId::Node(ast_variant_id, computation), constant_ref);
                    statics.infer.set_value_set(finished_value, set);

                    statics.infer.set_equal(finished_value, value_id, Reason::new(computation_node.loc, ReasonKind::IsOfType));
                }
                Err((message, call_stack)) => {
                    for &caller in call_stack.iter().rev().skip(1) {
                        statics.errors.info(caller, "".to_string());
                    }

                    statics.errors.error(*call_stack.last().unwrap(), message);
                    statics.infer.value_sets.get_mut(set).has_errors = true;
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
            let function_id = statics.program.insert_function(node_loc);

            let type_ = statics.infer.value_to_compiler_type(function_type);
            let ast_variant_ctx = statics.infer.value_sets.get_mut(set).ctx.take().unwrap();

            if let Some(symbol_name) = is_extern {
                statics.program.add_external_symbol(symbol_name);

                let routine = Routine::Extern(symbol_name);

                statics.thread_context.emitters.emit_routine(statics.program, function_id, &routine);
                statics.program.set_routine_of_function(function_id, Vec::new(), routine);
            } else {
                match time {
                    ExecutionTime::Never => return,
                    ExecutionTime::RuntimeFunc | ExecutionTime::Emission => {
                        let dependant_deps = &mut statics.infer.value_sets.get_mut(parent_set).ctx.as_mut().unwrap().emit_deps;
                        dependant_deps.add(node_loc, DepKind::Callable(function_id));

                        statics.program.queue_task(
                            ast_variant_ctx.emit_deps,
                            Task::EmitFunction(
                                statics.locals.clone(),
                                statics.infer.clone(),
                                statics.additional_info.clone(),
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
                            statics.thread_context,
                            statics.program,
                            statics.locals,
                            statics.infer,
                            ast.get(node_id),
                            statics.additional_info,
                            node_id,
                            ast_variant_id,
                            node_loc,
                            function_id,
                            true,
                        );
                    }
                }
            }

            statics.additional_info.insert((ast_variant_id, node_id), AdditionalInfoKind::Function(function_id));
            statics.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::BuiltinFunctionInTyping {
            node_id,
            function,
            parent_set,
            ast_variant_id,
        } => {
            let node = ast.get(node_id);
            let node_loc = node.loc;

            let function_id = statics.program.insert_defined_function(
                node_loc,
                Vec::new(),
                crate::ir::Routine::Builtin(function),
            );

            let routine = statics.program.get_routine(function_id).unwrap();
            statics.thread_context.emitters.emit_routine(statics.program, function_id, &routine);

            statics.additional_info.insert((ast_variant_id, node_id), AdditionalInfoKind::Function(function_id));
            statics.infer.value_sets.unlock(parent_set);
        }
        WaitingOnTypeInferrence::None => {},
    }
}

fn validate(types: &TypeSystem, errors: &mut ErrorCtx, target_checks: &Vec<TargetCheck>) -> bool {
    let mut has_errors = false;

    for check in target_checks {
        let &TypeKind::Target { min: subset, max: _ } = types.get(check.subset).kind() else { panic!() };
        let &TypeKind::Target { min: superset, max: _ } = types.get(check.superset).kind() else { panic!() };

        if (superset & subset) != subset {
            has_errors = true;
            errors.error(check.loc, "Target mismatch (temporary error message)".to_string());
        }
    }

    has_errors
}

fn build_constraints(
    statics: &mut Statics<'_, '_>,
    ast_variant_ctx: &mut AstVariantContext,
    ctx: &Context,
    node: NodeView<'_>,
    set: ValueSetId,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    statics.infer.set_value_set(node_type_id, set);
    statics.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, node.id);

    match node.node.kind {
        NodeKind::Uninit | NodeKind::Zeroed => {}
        NodeKind::PolymorphicArgument(index) => {
            statics.infer.value_sets.lock(set);

            let poly_param = &mut statics.poly_params[index];
            poly_param.used_as_value.get_or_insert(node_loc);
            if poly_param.check_for_dual_purpose(statics.errors) {
                statics.infer.value_sets.get_mut(set).has_errors |= true;
            }

            let sub_set = statics.infer.value_sets.add(WaitingOnTypeInferrence::None);
            let value_id = statics.infer.add_value(node_type_id, ());
            statics.infer.set_value_set(value_id, sub_set);
            statics.infer.set_equal(value_id, poly_param.value_id, Reason::new(node_loc, ReasonKind::Passed));

            statics.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::ConstantFromValueId {
                value_id,
                to: node.id,
                parent_set: set,
                ast_variant_id: ctx.ast_variant_id,
            });
        }
        NodeKind::AnonymousMember { name } => {
            statics.infer.value_sets.lock(set);
            let sub_set = statics.infer.value_sets.add(WaitingOnTypeInferrence::None);
            let unknown = statics.infer.add_unknown_type_with_set(sub_set);
            let value = statics.infer.add_type(TypeKind::Constant, Args([(node_type_id, Reason::temp(node_loc)), (unknown, Reason::temp(node_loc))]));
            statics.infer.set_value_set(value, sub_set);
            statics.infer.set_constant_field(unknown, name, node_type_id, Reason::temp(node_loc));
            statics.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::ConstantFromValueId {
                value_id: value,
                to: node.id,
                parent_set: set,
                ast_variant_id: ctx.ast_variant_id,
            });
        }
        NodeKind::Is => {
            let [expr, type_] = node.children.into_array();

            let got = build_type(statics, ast_variant_ctx, ctx, expr, set);

            let subset = statics.infer.value_sets.add(WaitingOnTypeInferrence::None);

            let mut sub_ctx = ctx.clone();
            sub_ctx.inside_type_comparison = true;
            let wanted = build_type(statics, ast_variant_ctx, &sub_ctx, type_, subset);

            let comparison_id = statics.infer.add_comparison(set, got, wanted);

            statics.additional_info.insert((ctx.ast_variant_id, node.id), AdditionalInfoKind::IsExpression(comparison_id));

            statics.infer.set_type(node_type_id, TypeKind::Bool, Args([]));
        }
        NodeKind::Tuple => {
            let mut values = Vec::with_capacity(node.children.len());
            for child in node.children {
                let child_id = build_constraints(statics, ast_variant_ctx, ctx, child, set);
                values.push((child_id, Reason::temp(node_loc)));
            }

            statics.infer.set_type(node_type_id, TypeKind::Tuple, Args(values));
        }
        NodeKind::Explain => {
            let [inner] = node.children.into_array();
            let inner = build_constraints(statics, ast_variant_ctx, ctx, inner, set);
            statics.infer.set_equal(node_type_id, inner, Reason::new(node_loc, ReasonKind::Passed));
            statics.needs_explaining.push((node.id, inner));
        }
        NodeKind::Pack => {
            let [inner] = node.children.into_array();
            let inner_type = build_constraints(statics, ast_variant_ctx, ctx, inner, set);
            statics.infer.set_pack(node_type_id, inner_type, Reason::temp(node_loc));
        }
        NodeKind::Unpack => {
            let [inner] = node.children.into_array();
            let inner_type = build_constraints(statics, ast_variant_ctx, ctx, inner, set);
            statics.infer.set_pack(inner_type, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::SizeOf => {
            let [inner] = node.children.into_array();
            let subset = statics.infer.value_sets.add(WaitingOnTypeInferrence::SizeOf { parent_set: set });
            build_type(statics, ast_variant_ctx, ctx, inner, subset);

            statics.infer.set_int(node_type_id, IntTypeKind::Usize);

            statics.infer.value_sets.lock(set);
        }
        NodeKind::Cast => {
            let [inner] = node.children.into_array();
            let result_value = build_constraints(statics, ast_variant_ctx, ctx, inner, set);
            statics.infer.set_cast(node_type_id, result_value, Reason::temp(node_loc));
        }
        NodeKind::BitCast => {
            let [value] = node.children.into_array();
            build_constraints(statics, ast_variant_ctx, ctx, value, set);
        }
        NodeKind::Empty => {
            // @Performance: We could set the type directly(because no inferrence has happened yet),
            // this is a roundabout way of doing things.
            let temp = statics.infer.add_type(type_infer::TypeKind::Empty, Args([]));
            statics.infer.set_equal(node_type_id, temp, Reason::new(node_loc, ReasonKind::IsOfType));
        }
        NodeKind::PolymorphicArgs => {
            let mut children = node.children.into_iter();
            let on = children.next().unwrap();
            let &NodeKind::Global { scope, name } = &on.kind else {
                todo!("Handling of the case where you pass polymorphic args to something that shouldn't have it");
            };

            statics.infer.set_value_set(TypeId::Node(ctx.ast_variant_id, on.id), set);
            statics.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, on.id);
            statics.infer.set_equal(TypeId::Node(ctx.ast_variant_id, on.id), node_type_id, Reason::temp(node_loc));

            let id = statics.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");
            build_global(statics, ast_variant_ctx, ctx, node.id, node.node, node.loc, id, Some(children), set, false);
        }
        NodeKind::Global { scope, name } => {
            let id = statics.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");
            build_global(statics, ast_variant_ctx, ctx, node.id, node.node, node.loc, id, None, set, false);
        }
        NodeKind::While {
            label: label_id,
        } => {
            let [iteration_var, condition, body, else_body] = node.children.into_array();

            let iteration_var_id = build_declarative_lvalue(statics, ast_variant_ctx, ctx, iteration_var, set, true);
            let int = statics.infer.add_int(IntTypeKind::Usize);
            statics.infer.set_equal(iteration_var_id, int, Reason::temp(node_loc));

            let label = statics.locals.get_label_mut(label_id);
            label.stack_frame_id = set;
            label.declared_at = Some(else_body.id);

            let condition_type_id = build_constraints(statics, ast_variant_ctx, ctx, condition, set);
            let bool_type = statics.infer.add_type(TypeKind::Bool, Args([]));
            statics.infer.set_equal(condition_type_id, bool_type, Reason::new(node_loc, ReasonKind::IsOfType));

            build_constraints(statics, ast_variant_ctx, ctx, body, set);

            let else_type = build_constraints(statics, ast_variant_ctx, ctx, else_body, set);

            statics.infer.set_equal(node_type_id, else_type, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::For {
            is_const: Some(_),
            label: label_id,
        } => {
            let [iterating, i_value, _inner, else_body] = node.children.into_array();

            let iteration_var_id = build_declarative_lvalue(statics, ast_variant_ctx, ctx, i_value, set, true);

            let label = statics.locals.get_label_mut(label_id);
            label.stack_frame_id = set;
            label.declared_at = Some(else_body.id);

            let usize_id = statics.infer.add_int(IntTypeKind::Usize);
            statics.infer.set_equal(iteration_var_id, usize_id, Reason::temp(node_loc));

            let iterator_type = build_constraints(statics, ast_variant_ctx, ctx, iterating, set);

            let check_type = statics.infer.add_unknown_type();
            let sub_set = statics.infer.value_sets.add(WaitingOnTypeInferrence::ConstFor {
                node_id: node.id,
                ast_variant_id: ctx.ast_variant_id,
                iterator_type: check_type,
                runs: ctx.runs,
                parent_set: set,
            });
            statics.infer.set_value_set(check_type, sub_set);
            statics.infer.set_equal(check_type, iterator_type, Reason::new(node_loc, ReasonKind::Passed));

            statics.infer.value_sets.lock(set);

            let else_type = build_constraints(statics, ast_variant_ctx, ctx, else_body, set);
            statics.infer.set_equal(node_type_id, else_type, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::For {
            is_const: None,
            label: label_id,
        } => {
            let [iterating, iteration_var, inner, else_body] = node.children.into_array();
            let [iterator, body] = inner.children.into_array();

            let iteration_var_id = build_declarative_lvalue(statics, ast_variant_ctx, ctx, iteration_var, set, true);
            let iterator_id = build_declarative_lvalue(statics, ast_variant_ctx, ctx, iterator, set, true);

            let label = statics.locals.get_label_mut(label_id);
            label.stack_frame_id = set;
            label.declared_at = Some(else_body.id);

            let usize_id = statics.infer.add_int(IntTypeKind::Usize);
            statics.infer.set_equal(iteration_var_id, usize_id, Reason::temp(node_loc));

            // The type the body returns doesn't matter, since we don't forward it.
            let iterating_type_id = build_constraints(statics, ast_variant_ctx, ctx, iterating, set);

            build_constraints(statics, ast_variant_ctx, ctx, body, set);

            statics.infer.set_for_relation(iterator_id, iterating_type_id, Reason::temp(node_loc));

            let else_type = build_constraints(statics, ast_variant_ctx, ctx, else_body, set);

            statics.infer.set_equal(node_type_id, else_type, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::Literal(Literal::Float(_)) => {
            statics.infer.set_type(node_type_id, TypeKind::Float, ());
        }
        NodeKind::Literal(Literal::Int(_)) => {
            statics.infer.set_type(node_type_id, TypeKind::Int, ());
        }
        NodeKind::Defer => {
            let [deferring] = node.children.into_array();
            build_constraints(statics, ast_variant_ctx, ctx, deferring, set);
            let empty_id = statics.infer.add_type(
                TypeKind::Empty, Args([]),
            );

            statics.infer.set_equal(node_type_id, empty_id, Reason::new(node_loc, ReasonKind::IsOfType));
        }
        NodeKind::Literal(Literal::String(_)) => {
            let u8_type = statics.infer.add_int(IntTypeKind::U8);
            statics.infer.set_type(node_type_id, TypeKind::Buffer, Args([(u8_type, Reason::temp(node_loc))]));
        }
        NodeKind::BuiltinFunction(function) => {
            let function_type_id = statics.infer.add_unknown_type();
            let sub_set = statics.infer.value_sets.add(WaitingOnTypeInferrence::BuiltinFunctionInTyping {
                node_id: node.id,
                function,
                parent_set: set,
                ast_variant_id: ctx.ast_variant_id,
            });

            // The parent value set has to wait for this function declaration to be emitted until
            // it can continue, so we lock it to make sure it doesn't get emitted before then.
            statics.infer.value_sets.lock(set);

            statics.infer.set_type(function_type_id, TypeKind::Function, ());
            statics.infer.set_value_set(function_type_id, sub_set);
            statics.infer.set_equal(node_type_id, function_type_id, Reason::new(node_loc, ReasonKind::IsOfType));
        }
        NodeKind::ArrayLiteral => {
            let inner_type = statics.infer.add_unknown_type_with_set(set);

            for arg in node.children.into_iter() {
                let arg_type_id = build_constraints(statics, ast_variant_ctx, ctx, arg, set);
                statics.infer.set_equal(arg_type_id, inner_type, Reason::new(node_loc, ReasonKind::Passed));
            }

            let usize = statics.infer.add_int(IntTypeKind::Usize);
            let length = statics.program.insert_buffer(&types::Type::new_int(IntTypeKind::Usize), (node.children.len()).to_le_bytes().as_ptr());

            let variable_count = statics.infer.add_value(
                usize,
                length,
            );
            statics.infer.set_value_set(variable_count, set);

            let array_type = statics.infer.add_type(
                TypeKind::Array, Args([(inner_type, Reason::temp(node_loc)), (variable_count, Reason::temp(node_loc))]),
            );
            // TODO: Is this necessary?
            statics.infer.set_value_set(array_type, set);

            statics.infer.set_equal(node_type_id, array_type, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::Member { name } => {
            let [of] = node.children.into_array();
            let of_type_id = build_constraints(statics, ast_variant_ctx, ctx, of, set);
            statics.infer
                .set_field_name_equal(of_type_id, name, node_type_id, Reason::new(node_loc, ReasonKind::NamedField(name)));
        }
        NodeKind::Local { local_id, .. } => {
            let local = statics.locals.get(local_id);
            let local_type_id = TypeId::Node(ctx.ast_variant_id, local.declared_at.unwrap());
            statics.infer
                .set_equal(local_type_id, node_type_id, Reason::new(node_loc, ReasonKind::LocalVariableIs(local.name)));

            if ctx.runs != ExecutionTime::Never && local.stack_frame_id != set {
                statics.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type". to_string());
                statics.infer.value_sets.get_mut(set).has_errors = true;
            }
        }
        NodeKind::If => {
            let [tags, condition, true_body, else_body] = node.children.into_array();

            let mut tags = build_tags(statics, ast_variant_ctx, ctx, tags, set);

            if let Some(_) = tags.compile.take() {
                let sub_set = statics.infer.value_sets.add(WaitingOnTypeInferrence::ConditionalCompilation {
                    node_id: node.id,
                    condition: condition.id,
                    true_body: true_body.id,
                    false_body: else_body.id,
                    ast_variant_id: ctx.ast_variant_id,
                    parent_set: set,
                    runs: ctx.runs,
                });
                statics.infer.value_sets.lock(set);

                let mut sub_ctx = ctx.clone();
                sub_ctx.runs = ctx.runs.combine(ExecutionTime::Typing);
                let condition_type_id = build_constraints(statics, ast_variant_ctx, &sub_ctx, condition, sub_set);

                let condition_type = statics.infer.add_type(TypeKind::Bool, Args([]));
                statics.infer
                    .set_equal(condition_type_id, condition_type, Reason::new(node_loc, ReasonKind::IsOfType));
            } else {
                let condition_type_id = build_constraints(statics, ast_variant_ctx, ctx, condition, set);
                let condition_type = statics.infer.add_type(TypeKind::Bool, Args([]));
                statics.infer
                    .set_equal(condition_type_id, condition_type, Reason::new(node_loc, ReasonKind::IsOfType));

                let true_body_id = build_constraints(statics, ast_variant_ctx, ctx, true_body, set);
                let false_body_id = build_constraints(statics, ast_variant_ctx, ctx, else_body, set);

                statics.infer
                    .set_equal(true_body_id, node_type_id, Reason::new(node_loc, ReasonKind::Passed));
                statics.infer
                    .set_equal(false_body_id, node_type_id, Reason::new(node_loc, ReasonKind::Passed));
            }

            tags.finish(statics, ast_variant_ctx, ctx, set);
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            let [operand] = node.children.into_array();
            let operand_type_id = build_constraints(statics, ast_variant_ctx, ctx, operand, set);

            let temp = statics.infer.add_type(
                TypeKind::Reference,
                Args([(node_type_id, Reason::new(node_loc, ReasonKind::Dereference))]),
            );
            statics.infer
                .set_equal(operand_type_id, temp, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::FunctionDeclaration { .. } => {
            build_function_declaration(statics, ast_variant_ctx, ctx, node, set, None);
        }
        NodeKind::ExpressiveFunctionCall => {
            let mut children = node.children.into_iter();
            let first_arg = children.next().unwrap();

            let calling = children.next().unwrap();
            let calling_type_id = TypeId::Node(ctx.ast_variant_id, calling.id);
            let meta_data = build_with_metadata(statics, ast_variant_ctx, ctx, calling, set);

            build_function_call(
                statics,
                ast_variant_ctx,
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
            let meta_data = build_with_metadata(statics, ast_variant_ctx, ctx, calling, set);

            build_function_call(
                statics, ast_variant_ctx, ctx,
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
            let left_type_id = build_declarative_lvalue(statics, ast_variant_ctx, ctx, left, set, false);
            let right_type_id = build_constraints(statics, ast_variant_ctx, ctx, right, set);

            statics.infer
                .set_equal(left_type_id, right_type_id, Reason::new(node_loc, ReasonKind::Assigned));

            statics.infer.set_type(
                node_type_id,
                TypeKind::Empty, Args([]),
            );
        }
        NodeKind::Binary { op } => {
            let [left, right] = node.children.into_array();
            let left = build_constraints(statics, ast_variant_ctx, ctx, left, set);
            let right = build_constraints(statics, ast_variant_ctx, ctx, right, set);

            // TODO: This is a massive hack! We want this to exist in the type inferrer itself probably....
            if op == BinaryOp::Equals || op == BinaryOp::NotEquals || op == BinaryOp::BitAnd || op == BinaryOp::BitOr {
                statics.infer.set_equal(left, right, Reason::temp(node_loc));
            }

            statics.infer.set_op_equal(op, left, right, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::Reference => {
            let [operand] = node.children.into_array();
            let inner = build_lvalue(statics, ast_variant_ctx, ctx, operand, set, true);
            statics.infer.set_type(
                node_type_id,
                TypeKind::Reference,
                Args([(inner, Reason::temp(node_loc))]),
            );
        }
        NodeKind::Block {
            label,
        } => {
            if let Some(label_id) = label {
                let label = statics.locals.get_label_mut(label_id);
                label.stack_frame_id = set;
                label.declared_at = node.children.into_iter().last().map(|v| v.id);
            }

            let mut children = node.children.into_iter();
            let tags_node = children.next().unwrap();
            let mut tags = build_tags(statics, ast_variant_ctx, ctx, tags_node, set);

            let mut sub_ctx = ctx.clone();
            if let Some((tag_loc, target)) = tags.target.take() {
                let required_type = statics.infer.add_type(TypeKind::Empty, Args([]));
                statics.infer.set_equal(node_type_id, required_type, Reason::temp(tag_loc));

                if let Some(parent) = ctx.target {
                    statics.target_checks.push(TargetCheck {
                        loc: tag_loc,
                        subset: target,
                        superset: parent,
                    });
                }
                sub_ctx.target = Some(target);
            }
            tags.finish(statics, ast_variant_ctx, &sub_ctx, set);

            let children_len = children.len();
            for statement_id in children.by_ref().take(children_len - 1) {
                build_constraints(statics, ast_variant_ctx, &sub_ctx, statement_id, set);
            }

            let last_type_id = build_constraints(statics, ast_variant_ctx, &sub_ctx, children.next().unwrap(), set);
            statics.infer
                .set_equal(node_type_id, last_type_id, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::Break {
            label,
            num_defer_deduplications: _,
        } => {
            let [value] = node.children.into_array();

            let label = statics.locals.get_label(label);
            if ctx.runs != ExecutionTime::Never && label.stack_frame_id != set {
                statics.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type".to_string());
                statics.infer.value_sets.get_mut(set).has_errors = true;
            }

            let label_type_id = TypeId::Node(ctx.ast_variant_id, label.declared_at.unwrap());

            let value_type_id = build_constraints(statics, ast_variant_ctx, ctx, value, set);
            statics.infer.set_equal(value_type_id, label_type_id, Reason::temp(node_loc));

            statics.infer.set_type(
                node_type_id,
                TypeKind::Empty, Args([]),
            );
        }
        NodeKind::Parenthesis => {
            let [inner] = node.children.into_array();
            let inner_type_id = build_constraints(statics, ast_variant_ctx, ctx, inner, set);
            statics.infer
                .set_equal(inner_type_id, node_type_id, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::Unary { op: _ } => {
            // @TODO: Make sure the types are valid for the operator
            let [operand] = node.children.into_array();
            let operand_id = build_constraints(statics, ast_variant_ctx, ctx, operand, set);

            statics.infer.set_equal(operand_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::TypeBound => {
            let [value, bound] = node.children.into_array();
            let value_type_id = build_constraints(statics, ast_variant_ctx, ctx, value, set);
            let bound_type_id = build_type(statics, ast_variant_ctx, ctx, bound, set);
            statics.infer
                .set_equal(node_type_id, bound_type_id, Reason::new(node_loc, ReasonKind::TypeBound));
            statics.infer
                .set_equal(value_type_id, node_type_id, Reason::new(node_loc, ReasonKind::Passed));
        }
        ref kind => {
            statics.errors.error(node_loc, format!("Invalid expression(it might only be valid as an lvalue, or as a type) {:?}", kind));
            statics.infer.value_sets.get_mut(set).has_errors |= true;
        }
    }

    node_type_id
}

fn extract_name(statics: &Statics<'_, '_>, node: NodeView<'_>) -> Option<(Ustr, Location)> {
    match node.kind {
        NodeKind::Local { local_id, .. } => {
            Some((statics.locals.get(local_id).name, node.loc))
        }
        NodeKind::TypeBound => {
            let [value, _] = node.children.into_array();
            extract_name(statics, value)
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
    fn finish(self, statics: &mut Statics<'_, '_>, _ast_variant_ctx: &mut AstVariantContext, _ctx: &Context, set: ValueSetId) {
        if let Some((loc, _)) = self.calling_convention {
            statics.errors.error(loc, format!("Tag not valid for this kind of expression"));
            statics.infer.value_sets.get_mut(set).has_errors = true;
        }

        if let Some((loc, _)) = self.target {
            statics.errors.error(loc, format!("Tag not valid for this kind of expression"));
            statics.infer.value_sets.get_mut(set).has_errors = true;
        }

        if let Some((loc, _, _)) = self.label {
            statics.errors.error(loc, format!("Tag not valid for this kind of expression"));
            statics.infer.value_sets.get_mut(set).has_errors = true;
        }

        if let Some(loc) = self.compile {
            statics.errors.error(loc, format!("Tag not valid for this kind of expression"));
            statics.infer.value_sets.get_mut(set).has_errors = true;
        }
    }
}

fn build_tags(
    statics: &mut Statics<'_, '_>,
    ast_variant_ctx: &mut AstVariantContext,
    ctx: &Context,
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
                    statics.errors.error(node.loc, format!("`call` defined twice"));
                    statics.infer.value_sets.get_mut(set).has_errors |= true;
                }
                let value = build_inferrable_constant_value(statics, ctx, inner, set);

                let builtin_id = statics.program
                    .get_member_id_from_builtin(Builtin::CallingConvention)
                    .expect("Parser should make sure we have access to calling convention");
                // TODO: It is scary to monomorphise something like this, since we have to give a node
                // that is the "global". Maybe there should be an entirely different code path for types?
                build_global(statics, ast_variant_ctx, ctx, inner.id, inner.node, inner.loc, builtin_id, None, set, true);

                tags.calling_convention = Some((
                    node.loc,
                    value.constant_value,
                ));
            }
            TagKind::Target => {
                let [inner] = node.children.into_array();
                if let Some(_) = tags.target {
                    statics.errors.error(node.loc, format!("`target` defined twice"));
                    statics.infer.value_sets.get_mut(set).has_errors |= true;
                }

                let mut sub_ast_variant_ctx = AstVariantContext {
                    // TODO: Think about whether this is correct or not
                    emit_deps: DependencyList::new(),
                };

                let mut sub_ctx = Context {
                    runs: ctx.runs.combine(ExecutionTime::Typing),
                    ast_variant_id: ctx.ast_variant_id,
                    inside_type_comparison: false,
                    // TODO: We don't ever use this thing....
                    target: None,
                };
                let sub_set = statics.infer.value_sets.add(WaitingOnTypeInferrence::None);

                build_constraints(statics, &mut sub_ast_variant_ctx, &mut sub_ctx, inner, sub_set);

                debug_assert!(sub_ast_variant_ctx.emit_deps.is_empty());

                let builtin_id = statics.program
                    .get_member_id_from_builtin(Builtin::Target)
                    .expect("Parser should make sure we have access to target");
                // TODO: It is scary to monomorphise something like this, since we have to give a node
                // that is the "global". Maybe there should be an entirely different code path for types?
                build_global(statics, &mut sub_ast_variant_ctx, &mut sub_ctx, inner.id, inner.node, inner.loc, builtin_id, None, sub_set, true);


                let target_id = TypeId::Node(ctx.ast_variant_id, node.id);
                statics.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::TargetFromConstantValue {
                    computation: inner.id,
                    value_id: target_id,
                    ast_variant_id: ctx.ast_variant_id,
                });

                statics.infer.set_value_set(target_id, set);

                tags.target = Some((
                    node.loc,
                    target_id,
                ));
            }
            TagKind::Compile => {
                if let Some(_) = tags.compile {
                    statics.errors.error(node.loc, format!("`const` defined twice"));
                    statics.infer.value_sets.get_mut(set).has_errors |= true;
                }

                tags.compile = Some(node.loc);
            }
            TagKind::Label(label_id) => {
                statics.locals.get_label_mut(label_id).declared_at = Some(node.id);
                tags.label = Some((node.loc, label_id, TypeId::Node(ctx.ast_variant_id, node.id)));
            }
        }
    }

    tags
}

fn build_function_declaration(
    statics: &mut Statics<'_, '_>,
    ast_variant_ctx: &mut AstVariantContext,
    ctx: &Context,
    node: NodeView<'_>,
    set: ValueSetId,
    mut wants_meta_data: Option<&mut FunctionMetaData>,
) {
    let &NodeKind::FunctionDeclaration { ref is_extern, ref argument_infos } = &node.node.kind else { unreachable!() };

    let sub_set = statics.infer.value_sets.add(WaitingOnTypeInferrence::None);

    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    let mut sub_ast_variant_ctx = AstVariantContext {
        emit_deps: DependencyList::new(),
    };
    let mut sub_ctx = Context {
        runs: ctx.runs.combine(ExecutionTime::RuntimeFunc),
        ast_variant_id: ctx.ast_variant_id,
        inside_type_comparison: false,
        target: None,
    };

    let mut children = node.children.into_iter();
    let mut tags = build_tags(statics, &mut sub_ast_variant_ctx, &mut sub_ctx, children.next().unwrap(), sub_set);

    statics.infer.value_sets.lock(set);

    let num_children = children.len();

    // @Cleanup: This isn't that nice
    let num_args = num_children - if is_extern.is_some() { 1 } else { 2 };

    if let Some(meta_data) = wants_meta_data.as_mut() {
        meta_data.arguments = Vec::with_capacity(num_args);
    }

    let mut function_args = FunctionArgsBuilder::with_num_args_capacity(num_args);
    for (argument_info, argument) in argument_infos.iter().zip(children.by_ref().take(num_args)) {
        let decl_id = build_declarative_lvalue(statics, &mut sub_ast_variant_ctx, &mut sub_ctx, argument, sub_set, true);
        function_args.add_arg((decl_id, Reason::temp(node.node.loc)));

        if let Some(meta_data) = wants_meta_data.as_mut() {
            meta_data.arguments.push(FunctionArgumentInfo {
                name: extract_name(statics, argument),
                var_args: argument_info.var_args,
            });
        } else {
            if let Some(loc) = argument_info.var_args {
                statics.errors.error(loc, format!("Cannot define var_args in this function, because it isn't bound to a constant (thus the var_args are lost)"));
                statics.infer.value_sets.get_mut(set).has_errors |= true;
            }
        }
    }

    let returns = children.next().unwrap();
    let returns_type_reason = Reason::new(returns.loc, ReasonKind::FunctionDeclReturnType);
    let returns_loc = returns.loc;
    let returns_type_id = build_type(statics, &mut sub_ast_variant_ctx, &mut sub_ctx, returns, sub_set);
    function_args.set_return((returns_type_id, returns_type_reason));

    if let Some((loc, target)) = tags.target.take() {
        function_args.set_target((target, Reason::temp(loc)));
        sub_ctx.target = Some(target);
    } else {
        let target = statics.infer.add_type(TypeKind::Target { min: TARGET_ALL, max: TARGET_ALL }, Args([]));
        function_args.set_target((target, Reason::temp(node.loc)));
    };

    if is_extern.is_none() {
        let body = children.next().unwrap();
        let body_type_id = build_constraints(statics, &mut sub_ast_variant_ctx, &mut sub_ctx, body, sub_set);

        statics.infer
            .set_equal(body_type_id, returns_type_id, Reason::new(returns_loc, ReasonKind::FunctionDeclReturned));
    };

    if let Some((loc, calling_convention)) = tags.calling_convention.take() {
        function_args.set_calling_convention((calling_convention, Reason::temp(loc)));
    } else {
        // TODO: This should be the borkle calling convention
        let constant_value = statics.program.insert_buffer(&types::Type::new_int(IntTypeKind::U8), (&0_u8) as *const u8);
        let calling_convention = statics.infer.add_type(TypeKind::ConstantValue(constant_value), Args([]));
        function_args.set_calling_convention((calling_convention, Reason::temp(node.loc)));
    }

    tags.finish(statics, ast_variant_ctx, ctx, sub_set);
    
    let infer_type_id = statics.infer.add_type(TypeKind::Function, Args(function_args.build()));
    statics.infer
        .set_equal(infer_type_id, node_type_id, Reason::new(node.node.loc, ReasonKind::FunctionDecl));

    statics.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::FunctionDeclaration {
        node_id: node.id,
        is_extern: *is_extern,
        function_type: infer_type_id,
        parent_set: set,
        time: ctx.runs,
        ast_variant_id: ctx.ast_variant_id,
    });

    let value_set = statics.infer.value_sets.get_mut(sub_set);
    let old_ast_variant_ctx = value_set.ctx.replace(sub_ast_variant_ctx);
    debug_assert!(old_ast_variant_ctx.is_none());
}

fn build_unique_type(
    statics: &mut Statics<'_, '_>,
    ast_variant_ctx: &mut AstVariantContext,
    ctx: &Context,
    node: NodeView<'_>,
    set: ValueSetId,
    marker: UniqueTypeMarker,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    match node.kind {
        NodeKind::EnumType { ref fields }=> {
            // TODO: These are ugly
            statics.infer.set_value_set(node_type_id, set);
            statics.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, node.id);

            let names = fields.to_vec().into_boxed_slice();
            let mut children = node.children.into_iter();
            let base_type = children.next().unwrap();
            let base_type_id = build_type(statics, ast_variant_ctx, ctx, base_type, set);

            let fields: Vec<_> = std::iter::once((base_type_id, Reason::temp(node_loc))).chain(children.map(|child| {
                let value = build_inferrable_constant_value(statics, ctx, child, set);
                statics.infer.set_equal(value.type_, base_type_id, Reason::temp(node_loc));

                (value.constant_value, Reason::temp(node_loc))
            })).collect();

            statics.infer.set_type(node_type_id, TypeKind::Enum(marker, names), Args(fields));
            statics.infer.set_value_set(node_type_id, set);
        }
        _ => {
            let inner_type = build_type(statics, ast_variant_ctx, ctx, node, set);
            let unique_type = statics.infer.add_type(
                TypeKind::Unique(marker),
                Args([(inner_type, Reason::temp(node.loc))]),
            );
            // TODO: Is this necessary?
            statics.infer.set_value_set(unique_type, set);
            return unique_type;
        }
    }

    node_type_id
}

fn build_type(
    statics: &mut Statics<'_, '_>,
    ast_variant_ctx: &mut AstVariantContext,
    ctx: &Context,
    node: NodeView<'_>,
    set: ValueSetId,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    statics.infer.set_value_set(node_type_id, set);
    statics.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, node.id);

    match node.kind {
        NodeKind::IntType => {
            if ctx.inside_type_comparison {
                let inner = statics.infer.add_type(TypeKind::CompareUnspecified, Args([]));
                statics.infer.set_type(node_type_id, TypeKind::Int, Args([(inner, Reason::temp_zero()), (inner, Reason::temp_zero())]));
            } else {
                statics.infer.set_type(node_type_id, TypeKind::Int, ());
            }
        }
        NodeKind::FloatType => {
            if ctx.inside_type_comparison {
                let inner = statics.infer.add_type(TypeKind::CompareUnspecified, Args([]));
                statics.infer.set_type(node_type_id, TypeKind::Float, Args([(inner, Reason::temp_zero())]));
            } else {
                statics.infer.set_type(node_type_id, TypeKind::Float, ());
            }
        }
        NodeKind::ImplicitType => {
            if ctx.inside_type_comparison {
                statics.infer.set_type(node_type_id, TypeKind::CompareUnspecified, Args([]));
            }
        },
        NodeKind::PolymorphicArgs => {
            let mut children = node.children.into_iter();
            let on = children.next().unwrap();
            let &NodeKind::Global { scope, name } = &on.kind else {
                todo!("Handling of the case where you pass polymorphic args to something that shouldn't have it");
            };

            statics.infer.set_value_set(TypeId::Node(ctx.ast_variant_id, on.id), set);
            statics.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, on.id);
            statics.infer.set_equal(TypeId::Node(ctx.ast_variant_id, on.id), node_type_id, Reason::temp(node_loc));

            let mut sub_ctx = ctx.clone();
            sub_ctx.runs = ctx.runs.combine(ExecutionTime::Never);
            let id = statics.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");
            build_global(statics, ast_variant_ctx, &sub_ctx, node.id, node.node, node.loc, id, Some(children), set, true);
        }
        NodeKind::Global { scope, name } => {
            let mut sub_ctx = ctx.clone();
            sub_ctx.runs = ctx.runs.combine(ExecutionTime::Never);
            let id = statics.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");
            build_global(statics, ast_variant_ctx, &sub_ctx, node.id, node.node, node.loc, id, None, set, true);
        }
        NodeKind::PolymorphicArgument(index) => {
            let poly_param = &mut statics.poly_params[index];
            poly_param.used_as_type.get_or_insert(node_loc);
            if poly_param.check_for_dual_purpose(statics.errors) {
                statics.infer.value_sets.get_mut(set).has_errors |= true;
            }
            statics.infer.set_equal(poly_param.value_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::Parenthesis | NodeKind::TypeAsValue => {
            let [inner] = node.children.into_array();
            let inner_type_id = build_type(statics, ast_variant_ctx, ctx, inner, set);
            statics.infer
                .set_equal(inner_type_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::LiteralType(ref type_) => {
            statics.infer.set_compiler_type(statics.program, node_type_id, type_);
        }
        NodeKind::FunctionType => {
            let mut children = node.children.into_iter();
            let mut tags = build_tags(statics, ast_variant_ctx, ctx, children.next().unwrap(), set);
            let mut function_args = FunctionArgsBuilder::with_num_args_capacity(children.len());
            let num_children = children.len();
            for type_node in children.by_ref().take(num_children - 1) {
                let type_id = build_type(statics, ast_variant_ctx, ctx, type_node, set);
                function_args.add_arg((type_id, Reason::temp(node_loc)));
            }

            let returns_type_id = build_type(statics, ast_variant_ctx, ctx, children.next().unwrap(), set);
            function_args.set_return((returns_type_id, Reason::temp(node_loc)));

            if let Some((loc, calling_convention)) = tags.calling_convention.take() {
                function_args.set_calling_convention((calling_convention, Reason::temp(loc)));
            } else {
                // TODO: This should be the borkle calling conventionTargei
                let constant_value = statics.program.insert_buffer(&types::Type::new_int(IntTypeKind::U8), (&0_u8) as *const u8);
                let calling_convention = statics.infer.add_type(TypeKind::ConstantValue(constant_value), Args([]));
                function_args.set_calling_convention((calling_convention, Reason::temp(node.loc)));
            }

            if let Some((loc, target)) = tags.target.take() {
                function_args.set_target((target, Reason::temp(loc)));
            } else {
                let target = statics.infer.add_type(TypeKind::Target { min: TARGET_ALL, max: TARGET_ALL }, Args([]));
                function_args.set_target((target, Reason::temp(node.loc)));
            }


            tags.finish(statics, ast_variant_ctx, ctx, set);

            let infer_type_id = statics.infer.add_type(TypeKind::Function, Args(function_args.build()));
            statics.infer
                .set_equal(infer_type_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::TupleType => {
            let mut values = Vec::with_capacity(node.children.len());
            for child in node.children {
                let child_id = build_type(statics, ast_variant_ctx, ctx, child, set);
                values.push((child_id, Reason::temp(node_loc)));
            }

            statics.infer.set_type(node_type_id, TypeKind::Tuple, Args(values));
        }
        NodeKind::EnumType { ref fields } => {
            let names = fields.to_vec().into_boxed_slice();
            let mut children = node.children.into_iter();
            let base_type = children.next().unwrap();
            let base_type_id = build_type(statics, ast_variant_ctx, ctx, base_type, set);

            let fields: Vec<_> = std::iter::once((base_type_id, Reason::temp(node_loc))).chain(children.map(|child| {
                let value = build_inferrable_constant_value(statics, ctx, child, set);
                statics.infer.set_equal(value.type_, base_type_id, Reason::temp(node_loc));

                (value.constant_value, Reason::temp(node_loc))
            })).collect();

            let marker = UniqueTypeMarker {
                name: None,
                loc: node_loc,
            };
            
            statics.infer.set_type(node_type_id, TypeKind::Enum(marker, names), Args(fields));
        }
        NodeKind::StructType { ref fields } => {
            // @Performance: Many allocations
            let names = fields.to_vec().into_boxed_slice();
            let fields: Vec<_> = node.children.into_iter().map(|v| (build_type(statics, ast_variant_ctx, ctx, v, set), Reason::temp(node_loc))).collect();
            statics.infer.set_type(node_type_id, TypeKind::Struct(names), Args(fields));
        }
        NodeKind::ReferenceType => {
            let [inner] = node.children.into_array();
            let inner = build_type(statics, ast_variant_ctx, ctx, inner, set);
            statics.infer.set_type(
                node_type_id,
                TypeKind::Reference, Args([(inner, Reason::temp(node_loc))]),
            );
        }
        NodeKind::BufferType => {
            let [inner] = node.children.into_array();
            let inner = build_type(statics, ast_variant_ctx, ctx, inner, set);
            statics.infer.set_type(
                node_type_id,
                TypeKind::Buffer, Args([(inner, Reason::temp(node_loc))]),
            );
        }
        NodeKind::ArrayType => {
            let [len, members] = node.children.into_array();
            let length = build_inferrable_constant_value(statics, ctx, len, set);
            let usize_type = statics.infer.add_int(IntTypeKind::Usize);
            statics.infer.set_equal(usize_type, length.type_, Reason::temp(node_loc));

            let member_type_id = build_type(statics, ast_variant_ctx, ctx, members, set);
            statics.infer.set_type(node_type_id, TypeKind::Array, Args([(member_type_id, Reason::temp(node_loc)), (length.constant, Reason::temp(node_loc))]));
        }
        NodeKind::TypeOf => {
            let [inner] = node.children.into_array();
            let mut sub_ctx = ctx.clone();
            sub_ctx.inside_type_comparison = false;
            sub_ctx.runs = ctx.runs.combine(ExecutionTime::Never);
            let type_ = build_constraints(statics, ast_variant_ctx, &sub_ctx, inner, set);
            statics.infer.set_equal(node_type_id, type_, Reason::new(node_loc, ReasonKind::TypeOf));
        }
        NodeKind::Local { local_id } => {
            statics.errors.info(statics.locals.get(local_id).loc, "Defined here".to_string());
            statics.errors.error(node_loc, "Cannot use a local as a type, did you intend to put a `typeof` before the local?".to_string());
            statics.infer.value_sets.get_mut(set).has_errors = true;
        }
        _ => {
            statics.errors.error(node_loc, format!("Expected a type, got {:?}", node.kind));
            statics.infer.value_sets.get_mut(set).has_errors = true;
        }
    }

    node_type_id
}

fn build_declarative_lvalue(
    statics: &mut Statics<'_, '_>,
    ast_variant_ctx: &mut AstVariantContext,
    ctx: &Context,
    node: NodeView<'_>,
    set: ValueSetId,
    is_declaring: bool,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    statics.infer.set_value_set(node_type_id, set);
    statics.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, node.id);

    match node.kind {
        NodeKind::Member { name } if !is_declaring => {
            let [of] = node.children.into_array();
            let of_type_id = build_lvalue(statics, ast_variant_ctx, ctx, of, set, false);
            statics.infer
                .set_field_name_equal(of_type_id, name, node_type_id, Reason::new(node_loc, ReasonKind::NamedField(name)));
        }
        NodeKind::Binary { op: BinaryOp::BitAnd } => {
            let [left, right] = node.children.into_array();

            let left_id = build_declarative_lvalue(statics, ast_variant_ctx, ctx, left, set, is_declaring);
            let right_id = build_declarative_lvalue(statics, ast_variant_ctx, ctx, right, set, is_declaring);

            statics.infer.set_equal(node_type_id, left_id, Reason::temp(node_loc));
            statics.infer.set_equal(node_type_id, right_id, Reason::temp(node_loc));
        }
        NodeKind::ImplicitType => {}
        NodeKind::Declare if !is_declaring => {
            let [inner] = node.children.into_array();
            let inner = build_declarative_lvalue(statics, ast_variant_ctx, ctx, inner, set, true);
            statics.infer.set_equal(node_type_id, inner, Reason::temp(node_loc));
        }
        NodeKind::Pack => {
            let [inner] = node.children.into_array();
            let inner_type = build_constraints(statics, ast_variant_ctx, ctx, inner, set);
            statics.infer.set_pack(node_type_id, inner_type, Reason::temp(node_loc));
        }
        NodeKind::Unpack => {
            let [inner] = node.children.into_array();
            let inner_type = build_constraints(statics, ast_variant_ctx, ctx, inner, set);
            statics.infer.set_pack(inner_type, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::Local{ local_id } => {
            if is_declaring {
                let local = statics.locals.get_mut(local_id);
                local.declared_at = Some(node.id);
                local.stack_frame_id = set;
                // Usage doesn't need to be set, because this is a declaration, and therefore mutability of the
                // variable doesn't matter yet.
            } else {
                let local = statics.locals.get(local_id);
                let local_type_id = TypeId::Node(ctx.ast_variant_id, local.declared_at.unwrap());
                statics.infer
                    .set_equal(local_type_id, node_type_id, Reason::new(node_loc, ReasonKind::LocalVariableIs(local.name)));
                if local.stack_frame_id != set {
                    statics.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type".to_string());
                    statics.infer.value_sets.get_mut(set).has_errors = true;
                }
            }
        }
        NodeKind::Parenthesis => {
            let [value] = node.children.into_array();
            let inner = build_declarative_lvalue(statics, ast_variant_ctx, ctx, value, set, is_declaring);
            statics.infer.set_equal(node_type_id, inner, Reason::temp(node_loc));
        }
        NodeKind::Tuple => {
            let mut values = Vec::with_capacity(node.children.len());
            for child in node.children {
                let child_id = build_declarative_lvalue(statics, ast_variant_ctx, ctx, child, set, is_declaring);
                values.push((child_id, Reason::temp(node_loc)));
            }

            statics.infer.set_type(node_type_id, TypeKind::Tuple, Args(values));
        }
        NodeKind::ArrayLiteral => {
            let inner_type = statics.infer.add_unknown_type_with_set(set);

            for arg in node.children.into_iter() {
                let arg_type_id = build_declarative_lvalue(statics, ast_variant_ctx, ctx, arg, set, is_declaring);
                statics.infer.set_equal(arg_type_id, inner_type, Reason::new(node_loc, ReasonKind::Passed));
            }

            let usize = statics.infer.add_int(IntTypeKind::Usize);
            let length = statics.program.insert_buffer(&types::Type::new_int(IntTypeKind::Usize), (node.children.len()).to_le_bytes().as_ptr());

            let variable_count = statics.infer.add_value(
                usize,
                length,
            );
            statics.infer.set_value_set(variable_count, set);

            let array_type = statics.infer.add_type(
                TypeKind::Array, Args([(inner_type, Reason::temp(node_loc)), (variable_count, Reason::temp(node_loc))]),
            );

            statics.infer.set_equal(node_type_id, array_type, Reason::new(node_loc, ReasonKind::Passed));
        }
        NodeKind::TypeBound => {
            let [value, bound] = node.children.into_array();
            // @Improvment: Here, both things are invariant. One of them could potentially be variant,
            // but only in some cases. After I think about how cases like this actually work,
            // I could try integrating this variance with the `access` variance passed in here to make it
            // less restrictive. It would also be nice if it was consistant with how non lvalue typebounds work,
            // since right now that's an inconsistancy that's going to be weird if you trigger it.
            let bound_type_id = build_type(statics, ast_variant_ctx, ctx, bound, set);
            statics.infer
                .set_equal(node_type_id, bound_type_id, Reason::temp(node_loc));
            let value_type_id = build_declarative_lvalue(statics, ast_variant_ctx, ctx, value, set, is_declaring);
            statics.infer
                .set_equal(value_type_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } if !is_declaring => {
            let [operand] = node.children.into_array();

            let temp = statics.infer.add_type(
                TypeKind::Reference,
                Args([(node_type_id, Reason::temp(node_loc))]),
            );

            let operand_type_id = build_constraints(statics, ast_variant_ctx, ctx, operand, set);
            statics.infer
                .set_equal(operand_type_id, temp, Reason::temp(node_loc));
        }
        _ => {
            statics.errors.error(node_loc, "Not a valid declarative lvalue".to_string());
            statics.infer.value_sets.get_mut(set).has_errors = true;
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
    statics: &mut Statics<'_, '_>,
    ast_variant_ctx: &mut AstVariantContext,
    ctx: &Context,
    node: NodeView<'_>,
    set: ValueSetId,
    can_reference_temporaries: bool,
) -> type_infer::ValueId {
    let node_loc = node.loc;
    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    match node.kind {
        NodeKind::Member { name } => {
            let [of] = node.children.into_array();
            let of_type_id = build_lvalue(statics, ast_variant_ctx, ctx, of, set, can_reference_temporaries);
            statics.infer
                .set_field_name_equal(of_type_id, name, node_type_id, Reason::new(node_loc, ReasonKind::NamedField(name)));
        }
        NodeKind::Local { local_id } => {
            let local = statics.locals.get(local_id);
            
            let local_type_id = TypeId::Node(ctx.ast_variant_id, local.declared_at.unwrap());
            statics.infer
                .set_equal(local_type_id, node_type_id, Reason::new(node_loc, ReasonKind::LocalVariableIs(local.name)));

            if local.stack_frame_id != set {
                statics.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type".to_string());
                statics.infer.value_sets.get_mut(set).has_errors = true;
            }
        }
        NodeKind::Parenthesis => {
            let [value] = node.children.into_array();
            let inner = build_lvalue(statics, ast_variant_ctx, ctx, value, set, can_reference_temporaries);
            statics.infer.set_equal(node_type_id, inner, Reason::temp(node_loc));
        }
        NodeKind::Pack => {
            let [inner] = node.children.into_array();
            let inner_type = build_constraints(statics, ast_variant_ctx, ctx, inner, set);
            statics.infer.set_pack(node_type_id, inner_type, Reason::temp(node_loc));
        }
        NodeKind::Unpack => {
            let [inner] = node.children.into_array();
            let inner_type = build_constraints(statics, ast_variant_ctx, ctx, inner, set);
            statics.infer.set_pack(inner_type, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::TypeBound => {
            let [value, bound] = node.children.into_array();
            // @Improvment: Here, both things are invariant. One of them could potentially be variant,
            // but only in some cases. After I think about how cases like this actually work,
            // I could try integrating this variance with the `access` variance passed in here to make it
            // less restrictive. It would also be nice if it was consistant with how non lvalue typebounds work,
            // since right now that's an inconsistancy that's going to be weird if you trigger it.
            let bound_type_id = build_type(statics, ast_variant_ctx, ctx, bound, set);
            statics.infer
                .set_equal(node_type_id, bound_type_id, Reason::temp(node_loc));
            let value_type_id = build_lvalue(statics, ast_variant_ctx, ctx, value, set, can_reference_temporaries);
            statics.infer
                .set_equal(value_type_id, node_type_id, Reason::temp(node_loc));
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            let [operand] = node.children.into_array();

            let temp = statics.infer.add_type(
                TypeKind::Reference,
                Args([(node_type_id, Reason::temp(node_loc))]),
            );

            let operand_type_id = build_constraints(statics, ast_variant_ctx, ctx, operand, set);
            statics.infer
                .set_equal(operand_type_id, temp, Reason::temp(node_loc));
        }
        _ => {
            if can_reference_temporaries {
                // Make it a reference to a temporary instead. This forces the pointer to be readonly.
                // TODO: Make it require it to be read-only here.
                return build_constraints(statics, ast_variant_ctx, ctx, node, set);
            } else {
                statics.errors.error(node_loc, "Not a valid lvalue, as this is assigned to, we can't use temporary values".to_string());
                statics.infer.value_sets.get_mut(set).has_errors = true;
            }
        }
    }

    statics.infer.set_value_set(node_type_id, set);
    statics.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, node.id);

    node_type_id
}

struct TypeSystemConstant {
    type_: TypeId,
    constant: TypeId,
    constant_value: TypeId,
}

// The first return is the type of the constant, the second return is the value id of that constant, where the constant will later be stored.
fn build_inferrable_constant_value(
    statics: &mut Statics<'_, '_>,
    ctx: &Context,
    node: NodeView<'_>,
    set: ValueSetId,
) -> TypeSystemConstant {
    let node_loc = node.loc;
    let node_id = node.id;
    let node_type_id = TypeId::Node(ctx.ast_variant_id, node.id);

    let type_system_constant = match node.kind {
        NodeKind::PolymorphicArgument(index) => {
            let constant_value = statics.infer.add_unknown_type_with_set(set);
            let constant = statics.infer.add_type(TypeKind::Constant, Args([(node_type_id, Reason::temp(node_loc)), (constant_value, Reason::temp(node_loc))]));
            let poly_param = &mut statics.poly_params[index];
            poly_param.used_as_value.get_or_insert(node_loc);
            if poly_param.check_for_dual_purpose(statics.errors) {
                statics.infer.value_sets.get_mut(set).has_errors |= true;
            }
            statics.infer.set_equal(poly_param.value_id, constant, Reason::temp(node_loc));
            
            TypeSystemConstant { type_: node_type_id, constant, constant_value }
        }
        NodeKind::ImplicitType => {
            if ctx.inside_type_comparison {
                let unspecified = statics.infer.add_type(TypeKind::CompareUnspecified, Args([]));
                let constant = statics.infer.add_type(TypeKind::Constant, Args([(node_type_id, Reason::temp(node_loc)), (unspecified, Reason::temp(node_loc))]));
                // TODO: Is this necessary?
                statics.infer.set_value_set(constant, set);

                TypeSystemConstant { type_: node_type_id, constant_value: unspecified, constant }
            } else {
                // Nothing at all is known about it, _except_ that the type of this node is equal to the
                // value.
                let constant_value = statics.infer.add_unknown_type_with_set(set);
                let constant = statics.infer.add_type(TypeKind::Constant, Args([(node_type_id, Reason::temp(node_loc)), (constant_value, Reason::temp(node_loc))]));
                // TODO: Is this necessary?
                statics.infer.set_value_set(constant, set);
                TypeSystemConstant { type_: node_type_id, constant_value, constant }
            }
        }
        _ => {
            // We can't figure it out in a clever way, so just compile time execute the node as a constant.
            let mut sub_ast_variant_ctx = AstVariantContext {
                // TODO: Think about whether this is correct or not
                emit_deps: DependencyList::new(),
            };
            let mut sub_ctx = Context {
                runs: ctx.runs.combine(ExecutionTime::Typing),
                ast_variant_id: ctx.ast_variant_id,
                inside_type_comparison: false,
                // TODO: We don't ever use this thing....
                target: None,
            };
            let sub_set = statics.infer.value_sets.add(WaitingOnTypeInferrence::None);

            let constant_type_id = build_constraints(statics, &mut sub_ast_variant_ctx, &mut sub_ctx, node, sub_set);
            debug_assert!(sub_ast_variant_ctx.emit_deps.is_empty());

            let constant_value = statics.infer.add_unknown_type_with_set(set);
            let value_id = statics.infer.add_type(TypeKind::Constant, Args([(constant_type_id, Reason::temp(node_loc)), (constant_value, Reason::temp(node_loc))]));
            // TODO: Is this necessary?
            statics.infer.set_value_set(value_id, set);
            statics.infer.set_equal(node_type_id, constant_type_id, Reason::temp(node_loc));

            statics.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::ValueIdFromConstantComputation {
                computation: node_id,
                value_id,
                ast_variant_id: ctx.ast_variant_id,
            });

            // Because the set of the node is already set by build_constraints, we early return type
            return TypeSystemConstant { type_: node_type_id, constant_value, constant: value_id };
        }
    };

    statics.infer.set_value_set(node_type_id, set);
    statics.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, node_id);

    type_system_constant
}

fn build_with_metadata(
    statics: &mut Statics<'_, '_>,
    ast_variant_ctx: &mut AstVariantContext,
    ctx: &Context,
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

            statics.infer.set_value_set(TypeId::Node(ctx.ast_variant_id, on.id), set);
            statics.infer.value_sets.add_node_to_set(set, ctx.ast_variant_id, on.id);
            statics.infer.set_equal(TypeId::Node(ctx.ast_variant_id, on.id), node_type_id, Reason::temp(node_loc));

            let id = statics.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");
            Some(build_global(statics, ast_variant_ctx, ctx, node.id, node.node, node.loc, id, Some(children), set, false))
        }
        NodeKind::Global { scope, name } => {
            let id = statics.program.get_member_id(scope, name).expect("The dependency system should have made sure that this is defined");
            Some(build_global(statics, ast_variant_ctx, ctx, node.id, node.node, node.loc, id, None, set, false))
        }
        _ => {
            build_constraints(statics, ast_variant_ctx, ctx, node, set);
            None
        }
    }
}

fn build_function_call<'a>(
    statics: &mut Statics<'_, '_>,
    ast_variant_ctx: &mut AstVariantContext,
    ctx: &Context,
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
                            statics.errors.error(name_loc, format!("Invalid argument name, `{}`", name));
                            statics.infer.value_sets.get_mut(set).has_errors |= true;
                            continue;
                        }
                    }
                }
                None => {
                    anonymous_index
                }
            };

            let arg_id = build_constraints(statics, ast_variant_ctx, ctx, arg, set);

            let Some(arg_info) = arguments.get(index) else {
                statics.errors.error(arg.loc, "Too many arguments passed to function".to_string());
                statics.infer.value_sets.get_mut(set).has_errors |= true;
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
                            statics.errors.info(var_args_loc, "Defined as a var_arg here".to_string());
                            statics.errors.info(prev_loc, "Assigned literally here".to_string());
                            statics.errors.error(arg.loc, "Cannot pass something both as a var_arg and as a literal value at once".to_string());
                            statics.infer.value_sets.get_mut(set).has_errors |= true;
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
                            statics.errors.info(prev_loc, "Previously defined here".to_string());
                            statics.errors.error(arg.loc, "Argument defined twice".to_string());
                            statics.infer.value_sets.get_mut(set).has_errors |= true;
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
                        let tuple_type = statics.infer.add_type(TypeKind::Tuple, Args([]));
                        statics.infer.set_value_set(tuple_type, set);
                        typer_args.add_arg((tuple_type, Reason::temp(node_loc)));
                    } else {
                        statics.errors.error(node_loc, format!("Argument `{}` not defined", i));
                        return;
                    }
                }
                ArgDefinedAs::Literal(node_loc, type_id) => {
                    typer_args.add_arg((type_id, Reason::temp(node_loc)));
                }
                ArgDefinedAs::VarArgs(node_loc, type_id) => {
                    let tuple_type = statics.infer.add_type(TypeKind::Tuple, Args(type_id));
                    statics.infer.set_value_set(tuple_type, set);
                    typer_args.add_arg((tuple_type, Reason::temp(node_loc)));
                }
            }
        }

        let calling_convention = statics.infer.add_unknown_type_with_set(set);
        typer_args.set_calling_convention((calling_convention, Reason::temp(node_loc)));

        let target = statics.infer.add_unknown_type_with_set(set);
        typer_args.set_target((target, Reason::temp(node_loc)));

        if let Some(parent) = ctx.target {
            statics.target_checks.push(TargetCheck {
                loc: node_loc,
                subset: parent,
                superset: target,
            });
        }

        // Specify that the caller has to be a function type
        let type_id = statics.infer.add_type(TypeKind::Function, Args(typer_args.build()));
        statics.infer.set_value_set(type_id, set);
        statics.additional_info.insert((ctx.ast_variant_id, node_id), AdditionalInfoKind::FunctionCall(function_arg_usage));
        statics.infer
            .set_equal(calling_type_id, type_id, Reason::new(node_loc, ReasonKind::FunctionCall));
    } else {
        let mut typer_args = FunctionArgsBuilder::with_num_args_capacity(children.size_hint().0);

        for arg in children {
            let arg_type_id = build_constraints(statics, ast_variant_ctx, ctx, arg, set);
            typer_args.add_arg((arg_type_id, Reason::new(node_loc, ReasonKind::FunctionCallArgument)));
        }

        let calling_convention = statics.infer.add_unknown_type_with_set(set);
        typer_args.set_calling_convention((calling_convention, Reason::temp(node_loc)));
        typer_args.set_return((node_type_id, Reason::new(node_loc, ReasonKind::FunctionCallReturn)));

        let target = statics.infer.add_unknown_type_with_set(set);
        typer_args.set_target((target, Reason::temp(node_loc)));

        if let Some(parent) = ctx.target {
            statics.target_checks.push(TargetCheck {
                loc: node_loc,
                subset: parent,
                superset: target,
            });
        }

        // Specify that the caller has to be a function type
        let type_id = statics.infer.add_type(TypeKind::Function, Args(typer_args.build()));
        statics.infer.set_value_set(type_id, set);
        statics.infer
            .set_equal(calling_type_id, type_id, Reason::new(node_loc, ReasonKind::FunctionCall));
    }
}

fn build_global<'a>(
    statics: &mut Statics<'_, '_>,
    ast_variant_ctx: &mut AstVariantContext,
    ctx: &Context,
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

    let (meta_data, member_kind) = statics.program.get_member_meta_data_and_kind(id);

    if matches!(member_kind, MemberKind::Type { .. }) != expecting_type {
        match member_kind {
            MemberKind::Const => {
                statics.errors.error(node.loc, format!("Cannot use `const` values in a type expression, did you intend to add a `typeof` in front?"));
            }
            MemberKind::Type { .. } => {
                statics.errors.error(node.loc, format!("Cannot use `type` values as expressions, they are only allowed in types."));
            }
        }
        statics.infer.value_sets.get_mut(set).has_errors |= true;
    }

    match id {
        PolyOrMember::Poly(id) => {
            let num_args = statics.program.get_num_poly_args(id);
            let other_yield_data = statics.program.get_polymember_yielddata(id);

            let mut param_values = Vec::with_capacity(num_args);
            let mut param_reasons = Vec::with_capacity(num_args);
            let sub_set = statics.infer.value_sets.add(WaitingOnTypeInferrence::None);

            if let Some(children) = children {
                if num_args != children.len() {
                    statics.errors.error(node_loc, format!("Passed {} arguments to polymorphic value, but the polymorphic value needs {} values", children.len(), num_args));
                    // @Cleanup: This should probably just be a function on TypeSystem
                    statics.infer.value_sets.get_mut(set).has_errors |= true;
                    return meta_data;
                }

                for (i, (param, other_poly_arg)) in children.zip(&other_yield_data.poly_params).enumerate() {
                    let param_loc = param.loc;
                    if other_poly_arg.is_type() {
                        let type_id = build_type(statics, ast_variant_ctx, ctx, param, sub_set);
                        param_values.push(type_id);
                        param_reasons.push((type_id, other_poly_arg.value_id, Reason::new(param_loc, ReasonKind::PolyParam(i))));
                    } else {
                        let param_value = build_inferrable_constant_value(statics, ctx, param, sub_set);
                        param_values.push(param_value.constant);
                        param_reasons.push((param_value.constant, other_poly_arg.value_id, Reason::new(param_loc, ReasonKind::PolyParam(i))));
                    }
                }
            } else {
                for (i, other_poly_arg) in other_yield_data.poly_params.iter().enumerate() {
                    if ctx.inside_type_comparison {
                        // @Copypasta
                        if other_poly_arg.is_type() {
                            let type_id = statics.infer.add_type(TypeKind::CompareUnspecified, Args([]));
                            statics.infer.set_value_set(type_id, sub_set);
                            param_values.push(type_id);
                            param_reasons.push((type_id, other_poly_arg.value_id, Reason::new(node_loc, ReasonKind::PolyParam(i))));
                        } else {
                            let unknown = statics.infer.add_unknown_type_with_set(sub_set);
                            let unspecified = statics.infer.add_type(TypeKind::CompareUnspecified, Args([]));
                            statics.infer.set_value_set(unspecified, sub_set);
                            let type_id = statics.infer.add_type(TypeKind::Constant, Args([(unknown, Reason::temp(node_loc)), (unspecified, Reason::temp(node_loc))]));
                            statics.infer.set_value_set(type_id, sub_set);
                            param_values.push(type_id);
                            param_reasons.push((type_id, other_poly_arg.value_id, Reason::new(node_loc, ReasonKind::PolyParam(i))));
                        }
                    } else {
                        let type_id = statics.infer.add_unknown_type_with_set(sub_set);
                        param_values.push(type_id);
                        param_reasons.push((type_id, other_poly_arg.value_id, Reason::new(node.loc, ReasonKind::PolyParam(i))));
                    }
                }
            }

            param_reasons.push((node_type_id, other_yield_data.root_value_id, Reason::new(node.loc, ReasonKind::PolyMember(id))));

            let poly_loc = statics.program.get_polymember_loc(id);

            statics.infer.add_subtree_from_other_typesystem(
                &other_yield_data.infer, 
                param_reasons.into_iter(),
                poly_loc,
            );

            statics.infer.value_sets.lock(set);

            if !ctx.inside_type_comparison {
                statics.infer.set_waiting_on_value_set(sub_set, WaitingOnTypeInferrence::MonomorphiseMember {
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
                statics.errors.error(node.loc, "Passed polymorphic parameters even though this value isn't polymorphic".to_string());
                // @Cleanup: This should probably just be a function on TypeSystem
                statics.infer.value_sets.get_mut(set).has_errors |= true;
                return meta_data;
            }

            let type_ = statics.program.get_member_type(id);

            let type_id = statics.infer.add_compiler_type(
                statics.program,
                &type_,
            );

            statics.infer.set_equal(node_type_id, type_id, Reason::new(node.loc, ReasonKind::IsOfType));

            match ctx.runs {
                // This will never be emitted anyway so it doesn't matter if the value isn't accessible.
                ExecutionTime::Never => {},
                ExecutionTime::RuntimeFunc => {
                    ast_variant_ctx.emit_deps.add(node.loc, DepKind::Member(id, MemberDep::Value));
                }
                ExecutionTime::Emission => {
                    ast_variant_ctx.emit_deps.add(node.loc, DepKind::Member(id, MemberDep::ValueAndCallableIfFunction));
                }
                ExecutionTime::Typing => {
                    // The parser should have already made sure the value is accessible. We will run this node
                    // through the emitter anyway though, so we don't have to make it into a constant or something.
                }
            }

            statics.additional_info.insert((ctx.ast_variant_id, node_id), AdditionalInfoKind::Monomorphised(id));
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
        // context: Context,
    },
    ConstFor {
        node_id: NodeId,
        ast_variant_id: AstVariantId,
        runs: ExecutionTime,
        iterator_type: TypeId,
        parent_set: ValueSetId,
        // context: Context,
    },
    SizeOf {
        parent_set: ValueSetId,
    },
    TargetFromConstantValue {
        computation: NodeId,
        ast_variant_id: AstVariantId,
        value_id: type_infer::ValueId,
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
