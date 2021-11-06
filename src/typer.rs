use crate::dependencies::{DepKind, DependencyList, MemberDep};
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::locals::{LocalId, LocalVariables};
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};
pub use crate::parser::{ast::Node, ast::NodeId, ast::NodeKind, Ast};
use crate::program::constant::ConstantRef;
use crate::program::{MemberMetaData, PolyOrMember, Program, Task};
use crate::thread_pool::ThreadContext;
use crate::type_infer::{self, Access, Reason, TypeSystem, ValueSetId, Variance};
use crate::types::{IntTypeKind, PtrPermits, Type, TypeKind};
use std::sync::Arc;

mod infer;

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
    locals: LocalVariables,
    /// Dependencies necessary for being able to emit code for this output.
    emit_deps: DependencyList,
    ast: Ast,
    infer: TypeSystem,
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
    let mut infer = TypeSystem::new();

    // Create type inference variables for all variables and nodes, so that there's a way to talk about
    // all of them.
    for node in &mut ast.nodes {
        node.type_infer_value_id = infer.add_unknown_type();
    }

    for local in locals.iter_mut() {
        local.type_infer_value_id = infer.add_unknown_type();
    }

    let mut ctx = Context {
        thread_context,
        errors,
        program,
        locals,
        emit_deps: from.emit_deps,
        ast,
        infer,
    };

    // Build the tree relationship between the different types.
    let root = ctx.ast.root;
    let root_value_set = ctx.infer.add_value_set(root);
    build_constraints(&mut ctx, root, root_value_set);

    loop {
        ctx.infer.solve();

        let mut progress = false;
        for value_set_id in ctx.infer.value_sets() {
            let value_set = ctx.infer.get_value_set_mut(value_set_id);
            if value_set_id == 0 // <- We don't want the base node, it's a special case, since it can't be dealt with by emit_execution_context; it can be any node.
            || value_set.has_errors
            || value_set.has_been_computed
            || value_set.uncomputed_values > 0
            {
                continue;
            }

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
            let value_set = ctx.infer.get_value_set_mut(value_set_id);
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

    println!("\nLocals:\n");
    for local in ctx.locals.iter() {
        println!(
            "{}: {}",
            local.name,
            ctx.infer.value_to_str(local.type_infer_value_id, 0)
        );
    }

    if ctx.infer.output_errors(ctx.errors) {
        return Err(());
    }

    let mut are_incomplete_sets = false;
    for value_set_id in ctx.infer.value_sets() {
        let value_set = ctx.infer.get_value_set_mut(value_set_id);
        if value_set.has_errors || value_set.uncomputed_values > 0 {
            println!("Set {} is uncomputable!", value_set_id);
            are_incomplete_sets = true;
        }
    }

    if are_incomplete_sets {
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

    Ok(Ok((ctx.emit_deps, ctx.locals, ctx.ast)))
}

fn emit_execution_context(ctx: &mut Context<'_, '_>, node_id: NodeId, set: ValueSetId) {
    let node = ctx.ast.get(node_id);
    let node_loc = node.loc;

    match node.kind {
        NodeKind::FunctionDeclarationInTyping {
            body,
            function_type,
            parent_set,
        } => {
            let type_ = ctx.infer.value_to_compiler_type(function_type);

            let function_id = ctx.program.insert_function(node_loc);

            // TODO: We want to only queue a task to emit the function later,
            // right now we emit it immediately though. Probably the
            // dependencies we emit aren't correct right now either.
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

            let function_id_buffer = ctx
                .program
                .insert_buffer(type_, &function_id as *const _ as *const u8);

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

            ctx.infer.unlock_value_set(parent_set);
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
    ctx.infer.add_node_to_set(set, node_id);

    match node.kind {
        NodeKind::Uninit | NodeKind::Zeroed | NodeKind::ImplicitType => {}
        NodeKind::Empty => {
            // @Performance: We could set the type directly(because no inferrence has happened yet),
            // this is a roundabout way of doing things.
            let temp = ctx.infer.add_type(
                type_infer::Empty,
                set,
                Reason::new(node_loc, "this value is empty"),
            );
            ctx.infer.set_equal(node_type_id, temp, Variance::Invariant);
        }
        NodeKind::Literal(Literal::Int(_)) => {
            // TODO: Actually add a constraint that checks that the type is an int, and that it's in bounds
        }
        NodeKind::Member { of, name } => {
            let of_type_id = build_constraints(ctx, of, set);
            ctx.infer
                .set_field_name_equal(of_type_id, name, node_type_id, Variance::Invariant);
        }
        NodeKind::Local(local_id) => {
            let local = ctx.locals.get(local_id);
            let local_type_id = local.type_infer_value_id;
            ctx.infer
                .set_equal(local_type_id, node_type_id, Variance::Invariant);

            if local.stack_frame_id != set {
                ctx.errors.error(node_loc, "Variable is defined in a different execution context, you cannot access it here, other than for its type". to_string());
                ctx.infer.make_value_set_erroneous(set);
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
                None => ctx.infer.add_type(
                    type_infer::Empty,
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
            // @Performance: It should be possible to constrain the type even here, but it's a little hairy.
            // Maybe a better approach would be just an "assignment" constraint, like "this type has to have this kind", or something
            let temp = ctx.infer.add_type(
                type_infer::Ref(
                    type_infer::Access::needs(Some(Reason::new(node_loc, "it was read from here")), None),
                    type_infer::Unknown
                ),
                set,
                Reason::new(node_loc, "it was dereferenced here"),
            );
            ctx.infer
                .set_equal(operand_type_id, temp, Variance::Invariant);
            ctx.infer
                .set_field_equal(temp, 1, node_type_id, Variance::Invariant);
        }
        NodeKind::FunctionDeclaration {
            ref args,
            returns,
            body,
        } => {
            // @Speed: Somewhat needless allocation
            let args = args.to_vec();

            let sub_set = ctx.infer.add_value_set(node_id);

            // The parent value set has to wait for this function declaration to be emitted until
            // it can continue, so we lock it to make sure it doesn't get emitted before then.
            ctx.infer.lock_value_set(set);

            let mut function_type_ids = Vec::with_capacity(args.len() + 1);
            let returns_type_id = build_constraints(ctx, returns, sub_set);
            function_type_ids.push(returns_type_id);

            for (local_id, type_node) in args {
                let local = ctx.locals.get_mut(local_id);
                local.stack_frame_id = sub_set;
                let local_type_id = local.type_infer_value_id;
                let type_id = build_constraints(ctx, type_node, sub_set);
                ctx.infer.set_value_set(local_type_id, sub_set);
                ctx.infer
                    .set_equal(type_id, local_type_id, Variance::Invariant);
                function_type_ids.push(type_id);
            }

            let body_type_id = build_constraints(ctx, body, sub_set);
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

            ctx.ast.get_mut(node_id).kind = NodeKind::FunctionDeclarationInTyping {
                body,
                function_type: infer_type_id,
                parent_set: set,
            };
        }
        NodeKind::FunctionCall { calling, ref args } => {
            // @Speed: Somewhat needless allocation
            let args = args.to_vec();

            let calling_loc = ctx.ast.get(calling).loc;
            let calling_type_id = build_constraints(ctx, calling, set);

            ctx.infer
                .set_field_equal(calling_type_id, 0, node_type_id, Variance::Invariant);

            for (i, &arg) in args.iter().enumerate() {
                let arg_type_id = build_constraints(ctx, arg, set);
                ctx.infer
                    .set_field_equal(calling_type_id, i + 1, arg_type_id, Variance::Covariant);
            }

            // Specify that the caller has to be a function type
            let infer_type = type_infer::ValueKind::Type(Some(type_infer::Type {
                kind: type_infer::TypeKind::Function,
                args: None,
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

            // @Performance: We could set the type directly(because no inferrence has happened yet),
            // this is a roundabout way of doing things.
            let temp = ctx.infer.add_type(type_infer::Empty, set, Reason::new(node_loc, "declaration return empty, however this reason should never be noticable by a user"));
            ctx.infer.set_equal(node_type_id, temp, Variance::Invariant);
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

            // @Performance: We could set the type directly(because no inferrence has happened yet),
            // this is a roundabout way of doing things.
            let temp = ctx.infer.add_type(
                type_infer::Empty,
                set,
                Reason::new(node_loc, "this assignment returns Empty"),
            );
            ctx.infer.set_equal(node_type_id, temp, Variance::Invariant);
        }
        NodeKind::Reference(operand) => {
            let access = ctx.infer.add_empty_access(set);
            let inner = build_lvalue(ctx, operand, access, set);
            let temp = ctx.infer.add_type(
                type_infer::Ref(type_infer::Var(access), type_infer::Var(inner)),
                set,
                Reason::new(node_loc, "of this reference operation"),
            );
            ctx.infer.set_equal(node_type_id, temp, Variance::Invariant);
        }
        NodeKind::Block {
            ref contents,
            label: _,
        } => {
            let last = *contents.last().unwrap();
            // @Performance: This isn't very fast, but it's fine for now
            for statement_id in contents[..contents.len() - 1].to_vec() {
                build_constraints(ctx, statement_id, set);
            }

            let last_type_id = build_constraints(ctx, last, set);
            ctx.infer
                .set_equal(node_type_id, last_type_id, Variance::Invariant);
        }
        NodeKind::Parenthesis(inner) => {
            let inner_type_id = build_constraints(ctx, inner, set);
            ctx.infer
                .set_equal(inner_type_id, node_type_id, Variance::Variant);
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
            // @Performance: We could set the type directly(because no inferrence has happened yet),
            // this is a roundabout way of doing things.
            let temp = ctx.infer.add_type(
                type_infer::CompilerType(type_),
                set,
                Reason::new(node_loc, "of this type"),
            );
            ctx.infer.set_equal(node_type_id, temp, Variance::Invariant);
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

            let infer_type = type_infer::ValueKind::Type(Some(type_infer::Type {
                kind: type_infer::TypeKind::Function,
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
                type_infer::ValueKind::Type(Some(type_infer::Type {
                    kind: type_infer::TypeKind::Struct(names),
                    args: Some(fields),
                })),
                set,
                Reason::new(node_loc, "of this type"),
            );
            ctx.infer.set_equal(node_type_id, temp, Variance::Invariant);
        }
        // @Improvement: Reference type permits can be inferred as well, but that's not represented here.
        NodeKind::ReferenceType(inner, permits) => {
            let inner = build_constraints(ctx, inner, set);
            // TODO: It would be nice to specify the location of the permit specification, so we can generate
            // an error that points to them specifically
            let access = permits_to_access(permits);
            let temp = ctx.infer.add_type(
                type_infer::Ref(access, type_infer::Var(inner)),
                set,
                Reason::new(node_loc, "of this reference type"),
            );
            ctx.infer.set_equal(node_type_id, temp, Variance::Invariant);
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
                ctx.infer.make_value_set_erroneous(set);
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
            let operand_type_id = build_constraints(ctx, operand, set);
            // @Performance: It should be possible to constrain the type even here, but it's a little hairy.
            // Maybe a better approach would be just an "assignment" constraint, like "this type has to have this kind", or something
            let temp = ctx.infer.add_type(
                type_infer::Ref(type_infer::Var(access), type_infer::Unknown),
                set,
                Reason::new(node_loc, "it is dereferenced here"),
            );
            // @Correctness: I'm not sure that a variance here is correct in all
            // cases, but without it the inferrence isn't correct.
            // But I think it's correct, because essentially what this is saying is "this pointer needs
            // at least the permissions to do the things we're trying to do, but if it has more that is fine",
            // and that should be ok, right?
            ctx.infer
                .set_equal(operand_type_id, temp, Variance::Variant);
            ctx.infer
                .set_field_equal(temp, 1, node_type_id, Variance::Invariant);
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

    node_type_id
}
