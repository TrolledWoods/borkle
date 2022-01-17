use crate::ir::{Instr, LabelId, StackAllocator, Routine, UserDefinedRoutine, StackValue, PrimitiveType, TypedLayout};
use crate::layout::StructLayout;
use crate::location::Location;
use crate::literal::Literal;
use crate::locals::LocalVariables;
use crate::operators::{BinaryOp, UnaryOp};
use crate::parser::{Ast, NodeKind, NodeView};
use crate::ast::NodeId;
use crate::program::{FunctionId, Program, constant::ConstantRef};
use crate::thread_pool::ThreadContext;
use crate::type_infer::{ValueId as TypeId, TypeSystem, Reason, Args, AstVariantId, self, Layout};
use crate::typer::{AdditionalInfo, AdditionalInfoKind, FunctionArgUsage};
use crate::types::{Type, TypeKind, IntTypeKind};

/// Emit instructions for an Ast.
pub fn emit<'a>(
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    locals: &mut LocalVariables,
    types: &mut TypeSystem,
    ast: &Ast,
    additional_info: &AdditionalInfo,
    node: NodeId,
    variant_id: AstVariantId,
) -> (Vec<FunctionId>, UserDefinedRoutine) {
    let mut ctx = Context {
        thread_context,
        instr: Vec::new(),
        registers: StackAllocator::new(),
        locals,
        types,
        program,
        label_locations: Vec::new(),
        calling: Vec::new(),
        last_location: None,
        variant_id,
        additional_info,

        defers: Vec::new(),
    };

    let body_id = TypeId::Node(ctx.variant_id, node);
    let result = emit_node(&mut ctx, ast.get(node));
    let result_layout = ctx.to_typed_layout(body_id);

    /*println!("The instructions are: ");
    for instr in &ctx.instr {
        println!("{:?}", instr);
    }*/

    (
        ctx.calling,
        UserDefinedRoutine {
            loc: ast.root().loc,
            name: ast.name,
            instr: ctx.instr,
            stack: ctx.registers,
            result,
            args: Vec::new(),
            result_layout,
            label_locations: ctx.label_locations,
        },
    )
}

pub fn emit_function_declaration<'a>(
    thread_context: &mut ThreadContext<'a>,
    program: &'a Program,
    locals: &mut LocalVariables,
    types: &mut TypeSystem,
    ast: &Ast,
    additional_info: &AdditionalInfo,
    node_id: NodeId,
    variant_id: AstVariantId,
    type_: Type,
    loc: Location,
    function_id: FunctionId,
) {
    let mut ctx = Context {
        thread_context,
        instr: Vec::new(),
        registers: StackAllocator::new(),
        locals,
        types,
        program,
        variant_id,
        label_locations: Vec::new(),
        defers: Vec::new(),
        calling: Vec::new(),
        last_location: None,
        additional_info,
    };

    let function_type = ctx.types.get(TypeId::Node(ctx.variant_id, node_id));
    let args = function_type.args();

    debug_assert_eq!(function_type.kind(), &type_infer::TypeKind::Function);

    // Pretend there are actual values on the stack
    // @Performance
    let args: Vec<_> = args.to_vec().into_iter().skip(1).map(|v| {
        ctx.create_reg_and_typed_layout(v)
    }).collect();

    let node = ast.get(node_id);
    let mut children = node.children.into_iter();
    for &(passed_as, _) in args.iter() {
        let child = children.next().unwrap();
        emit_declarative_lvalue(&mut ctx, child, passed_as, true);
    }

    // Now that we've read all the arguments of the function, only the return type,
    // and the body are left. We don't need the return type, as that is only for the typer,
    // so we skip that one.

    let body = children.nth(1).unwrap();
    let body_id = TypeId::Node(ctx.variant_id, body.id);
    let result = emit_node(&mut ctx, body);
    let result_layout = ctx.to_typed_layout(body_id);

    /*println!("The instructions are: ");
    for instr in &ctx.instr {
        println!("{:?}", instr);
    }*/

    let routine = Routine::UserDefined(UserDefinedRoutine {
        loc,
        name: ast.name,
        label_locations: ctx.label_locations,
        instr: ctx.instr,
        stack: ctx.registers,
        args,
        result,
        result_layout,
    });

    let TypeKind::Function { args, returns } = type_.kind() else { unreachable!() };
    ctx.thread_context.emitters.emit_routine(ctx.program, function_id, &routine, args, *returns);

    ctx
        .program
        .set_routine_of_function(function_id, ctx.calling, routine);
}

fn emit_node<'a>(ctx: &mut Context<'a, '_>, mut node: NodeView<'a>) -> StackValue {
    ctx.emit_debug(node.loc);

    let node_type_id = TypeId::Node(ctx.variant_id, node.id);

    match &node.kind {
        NodeKind::Empty => StackValue::ZST,
        NodeKind::Break {
            label: label_id,
            num_defer_deduplications,
        } => {
            let [value] = node.children.as_array();
            
            let label = ctx.locals.get_label(*label_id);
            let ir_label = label.ir_labels.as_ref().unwrap()[*num_defer_deduplications];
            let label_value = label.value.unwrap();

            // @Temporary
            let from_layout = *ctx.types.get(TypeId::Node(ctx.variant_id, value.id)).layout.unwrap();
            let from = emit_node(ctx, value);

            for defer_index in (ctx.locals.get_label(*label_id).defer_depth
                + *num_defer_deduplications..ctx.defers.len())
                .rev()
            {
                emit_node(ctx, ctx.defers[defer_index].clone());
            }

            ctx.emit_move(label_value, from, from_layout);
            ctx.emit_jump(ir_label);

            StackValue::ZST
        }
        NodeKind::For {
            is_const: Some(_),
            label,
        } => {
            let [iterating, i_value_decl, mut inner, else_body] = node.children.as_array();

            let &AdditionalInfoKind::ConstForAstVariants { referenced, ref variant_ids } = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };

            let end_label = ctx.create_label();

            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            ctx.locals.get_label_mut(*label).value = Some(to);

            // Set up iterator values
            let i_value = ctx.create_reg(TypeId::Node(ctx.variant_id, i_value_decl.id));
            ctx.emit_move_imm(i_value, 0_usize.to_le_bytes(), Layout::USIZE);

            // TODO: Figure out how to abstract this.
            if referenced {
                let iterating_value_ptr = emit_node(ctx, iterating.clone());

                let mut old_field_offset = 0;
                let mut iterating_value_fields = StructLayout::new(0);
                for &variant_id in variant_ids.iter() {
                    let [v_value_decl, body] = inner.children.as_array();

                    let field_layout = *ctx.types.get(TypeId::Node(variant_id, v_value_decl.id)).layout.unwrap();
                    let new_field_offset = iterating_value_fields.next(field_layout);
                    if new_field_offset != old_field_offset {
                        ctx.emit_binary_imm_u64(BinaryOp::Add, iterating_value_ptr, iterating_value_ptr, (new_field_offset - old_field_offset) as u64);
                    }
                    old_field_offset = new_field_offset;

                    emit_declarative_lvalue(ctx, i_value_decl.clone(), i_value, true);

                    let old_variant_id = ctx.variant_id;
                    ctx.variant_id = variant_id;
                    emit_declarative_lvalue(ctx, v_value_decl, iterating_value_ptr, true);
                    emit_node(ctx, body);
                    ctx.variant_id = old_variant_id;

                    ctx.emit_binary_imm_u64(BinaryOp::Add, i_value, i_value, 1);
                }
            } else {
                let iterating_value = emit_node(ctx, iterating.clone());

                let mut iterating_value_fields = StructLayout::new(0);
                for &variant_id in variant_ids.iter() {
                    emit_declarative_lvalue(ctx, i_value_decl.clone(), i_value, true);

                    let [v_value_decl, body] = inner.children.as_array();

                    let field_layout = *ctx.types.get(TypeId::Node(variant_id, v_value_decl.id)).layout.unwrap();
                    let field_offset = iterating_value_fields.next(field_layout);

                    let old_variant_id = ctx.variant_id;
                    ctx.variant_id = variant_id;
                    emit_declarative_lvalue(ctx, v_value_decl, get_member(iterating_value, field_offset), true);
                    emit_node(ctx, body);
                    ctx.variant_id = old_variant_id;

                    ctx.emit_binary_imm_u64(BinaryOp::Add, i_value, i_value, 1);
                }
            }

            let evaluate_to = emit_node(ctx, else_body);
            ctx.emit_move(to, evaluate_to, to_layout);
            ctx.define_label(end_label);
            evaluate_to
        }
        NodeKind::For {
            is_const: None,
            label,
        } => {
            let [iterating, i_value_decl, mut inner, else_body] = node.children.as_array();
            let [v_value_decl, body] = inner.children.as_array();

            let end_label = ctx.create_label();
            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            ctx.locals.get_label_mut(*label).value = Some(to);
            ctx.locals.get_label_mut(*label).ir_labels = Some(vec![end_label]);

            let mut iterating_value = emit_node(ctx, iterating.clone());

            // Set up iterator values
            let i_value = ctx.create_reg(TypeId::Node(ctx.variant_id, i_value_decl.id));
            ctx.emit_move_imm(i_value, 0_usize.to_le_bytes(), Layout::USIZE);

            let mut by_value = true;

            let mut iterator_type_id = TypeId::Node(ctx.variant_id, iterating.id);
            if let type_infer::TypeKind::Reference = ctx.types.get(iterator_type_id).kind() {
                iterator_type_id = ctx.types.get(iterator_type_id).args()[0];
                by_value = false;
            }

            let pointee_layout;

            let (current, end) = match ctx.types.get(iterator_type_id).kind() {
                type_infer::TypeKind::Array => {
                    let iterator_type = ctx.types.get(iterator_type_id);
                    let iterator_args = iterator_type.args();
                    let element_type = iterator_args[0];
                    let length = unsafe { *ctx.types.extract_constant_temp(iterator_args[1]).unwrap().as_ptr().cast::<usize>() };

                    let ptr_to_array = if by_value {
                        let array_ptr_type_id = ctx.types.add_type(type_infer::TypeKind::Reference, type_infer::Args([(iterator_type_id, Reason::temp_zero())]), ());
                        let temp = ctx.create_reg(array_ptr_type_id);
                        ctx.emit_reference(temp, iterating_value);
                        temp
                    } else {
                        iterating_value
                    };

                    pointee_layout = *ctx.types.get(element_type).layout.unwrap();

                    let first_element = ctx.create_reg_with_layout(Layout::PTR);
                    let last_element  = ctx.create_reg_with_layout(Layout::PTR);
                    ctx.emit_move(first_element, ptr_to_array, Layout::PTR);
                    ctx.emit_binary_imm_u64(BinaryOp::Add, last_element, first_element, (length * pointee_layout.size) as u64);

                    (first_element, last_element)
                }
                type_infer::TypeKind::Buffer => {
                    let pointee = ctx.types.get(iterator_type_id).args()[0];

                    if !by_value {
                        let (new_iterating, layout) = ctx.create_reg_and_layout(iterator_type_id);
                        ctx.emit_dereference(new_iterating, iterating_value, layout);
                        iterating_value = new_iterating;
                    }

                    pointee_layout = *ctx.types.get(pointee).layout.unwrap();

                    let current = ctx.create_reg_with_layout(Layout::PTR);
                    let end     = ctx.create_reg_with_layout(Layout::PTR);

                    ctx.emit_move(current, get_member(iterating_value, 0), Layout::PTR);
                    ctx.emit_move(end,     get_member(iterating_value, 0), Layout::PTR);
                    ctx.emit_incr_ptr(end, get_member(iterating_value, 8), pointee_layout.size);

                    (current, end)
                }
                _ => unreachable!(),
            };

            let condition = ctx.create_reg_with_layout(Layout::BOOL);

            let condition_label = ctx.create_label();
            ctx.define_label(condition_label);

            ctx.emit_binary(BinaryOp::LessThan, condition, current, end, PrimitiveType::U64);

            let else_body_label = ctx.create_label();
            ctx.emit_jump_if_zero(condition, else_body_label);

            emit_declarative_lvalue(ctx, i_value_decl, i_value, true);

            if by_value {
                let (temp, layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, v_value_decl.id));
                ctx.emit_dereference(temp, current, layout);
                emit_declarative_lvalue(ctx, v_value_decl, temp, true);
            } else {
                emit_declarative_lvalue(ctx, v_value_decl, current, true);
            }
            emit_node(ctx, body);

            ctx.emit_binary_imm_u64(BinaryOp::Add, current, current, pointee_layout.size as u64);
            ctx.emit_binary_imm_u64(BinaryOp::Add, i_value, i_value, 1);

            ctx.emit_jump(condition_label);

            ctx.define_label(else_body_label);

            let else_body_from = emit_node(ctx, else_body);
            ctx.emit_move(to, else_body_from, to_layout);

            ctx.define_label(end_label);

            to
        }
        NodeKind::While {
            label,
        } => {
            let [i_value_decl, condition, body, else_body] = node.children.as_array();

            let end_label = ctx.create_label();
            let else_body_label = ctx.create_label();

            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            let label = ctx.locals.get_label_mut(*label);
            label.value = Some(to);
            label.ir_labels = Some(vec![end_label]);

            let i_value = ctx.create_reg(TypeId::Node(ctx.variant_id, i_value_decl.id)); 
            ctx.emit_move_imm(i_value, 0_usize.to_le_bytes(), Layout::USIZE);

            // Condition
            let condition_label = ctx.create_label();
            ctx.define_label(condition_label);

            emit_declarative_lvalue(ctx, i_value_decl, i_value, true);

            let condition = emit_node(ctx, condition);
            ctx.emit_jump_if_zero(condition, else_body_label);

            // Loop body
            emit_node(ctx, body);
            ctx.emit_binary_imm_u64(BinaryOp::Add, i_value, i_value, 1);
            ctx.emit_jump(condition_label);

            // Else body
            ctx.define_label(else_body_label);

            let else_body_value = emit_node(ctx, else_body);
            ctx.emit_move(to, else_body_value, to_layout);

            // End
            ctx.define_label(end_label);

            to
        }
        NodeKind::If {
            is_const: None,
        } => {
            let [condition, true_body, false_body] = node.children.as_array();

            let condition = emit_node(ctx, condition);

            let start_of_false_body = ctx.create_label();
            let end_of_false_body = ctx.create_label();

            ctx.emit_jump_if_zero(condition, start_of_false_body);

            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));

            // True body
            let true_body = emit_node(ctx, true_body);
            ctx.emit_move(to, true_body, to_layout);
            ctx.emit_jump(end_of_false_body);

            // False body
            ctx.define_label(start_of_false_body);
            let false_body = emit_node(ctx, false_body);
            ctx.emit_move(to, false_body, to_layout);

            ctx.define_label(end_of_false_body);

            to
        }
        NodeKind::Literal(Literal::String(data)) => {
            let u8_type = Type::new(TypeKind::Int(IntTypeKind::U8));
            let type_ = Type::new(TypeKind::Buffer { pointee: u8_type });
            let ptr = ctx.program.insert_buffer(
                type_,
                &crate::types::BufferRepr {
                    ptr: data.as_ptr() as *mut _,
                    length: data.len(),
                } as *const _ as *const _,
            );

            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_global(to, ptr, to_layout);
            to
        }
        NodeKind::Literal(Literal::Int(num)) => {
            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_move_imm(to, (*num as u64).to_le_bytes(), to_layout);
            to
        }
        &NodeKind::Literal(Literal::Float(num)) => {
            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            match to_layout.size {
                4 => {
                    let bytes = ((num as f32).to_bits() as u64).to_le_bytes();
                    ctx.emit_move_imm(to, bytes, to_layout);
                }
                8 => {
                    let bytes = num.to_bits().to_le_bytes();
                    ctx.emit_move_imm(to, bytes, to_layout);
                }
                _ => unreachable!(),
            }

            to
        }
        NodeKind::Zeroed => {
            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_set_to_zero(to, to_layout);
            to
        }
        NodeKind::Uninit => {
            // We don't need an instruction to initialize the memory, because it's uninit!
            ctx.create_reg(TypeId::Node(ctx.variant_id, node.id))
        }
        NodeKind::Cast => {
            let [value] = node.children.as_array();
            let from = emit_node(ctx, value.clone());
            let to = ctx.create_reg(TypeId::Node(ctx.variant_id, node.id));

            // Get the types of the values
            let node_type = ctx.types.get(TypeId::Node(ctx.variant_id, node.id));
            let value_type = ctx.types.get(TypeId::Node(ctx.variant_id, value.id));

            match (node_type.kind, value_type.kind) {
                (
                    Some(type_infer::Type { kind: type_infer::TypeKind::Int, args: Some(_) }),
                    Some(type_infer::Type { kind: type_infer::TypeKind::Int, args: Some(_) }),
                ) => {
                    let to_number = ctx.to_number_type(TypeId::Node(ctx.variant_id, node.id)).unwrap();
                    let from_number = ctx.to_number_type(TypeId::Node(ctx.variant_id, value.id)).unwrap();

                    ctx.emit_convert_num(to, to_number, from, from_number);
                }
                (
                    Some(type_infer::Type { kind: type_infer::TypeKind::Buffer, args: Some(_) }),
                    Some(type_infer::Type { kind: type_infer::TypeKind::Reference, args: Some(from_args) })
                ) => {
                    match ctx.types.get(from_args[0]).kind {
                        Some(type_infer::Type { kind: type_infer::TypeKind::Array, args: Some(array_args) }) => {
                            let length = ctx.types.extract_constant_temp(array_args[1]).unwrap();

                            ctx.emit_move(get_member(to, 0), from, Layout::PTR);
                            ctx.emit_global(get_member(to, 8), length, Layout::USIZE);
                        }
                        _ => unreachable!("Internal error: Invalid types for cast reached emission"),
                    }
                }
                (
                    Some(type_infer::Type { kind: type_infer::TypeKind::Reference, .. }),
                    Some(type_infer::Type { kind: type_infer::TypeKind::Reference, .. }),
                ) => {
                    ctx.emit_move(to, from, Layout::PTR);
                }
                _ => unreachable!("Internal error: Invalid types for cast reached emission"),
            }

            to
        }
        NodeKind::BitCast => {
            let [value] = node.children.as_array();
            emit_node(ctx, value)
        }
        NodeKind::Constant(bytes, _) => {
            if let type_infer::TypeKind::Function { .. } = ctx.types.get(TypeId::Node(ctx.variant_id, node.id)).kind() {
                let function_id = unsafe { *(bytes.as_ptr() as *const FunctionId) };
                if !ctx.calling.contains(&function_id) {
                    ctx.calling.push(function_id);
                }
            }

            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_global(to, *bytes, to_layout);

            to
        }
        NodeKind::Member { name } => {
            let [of] = node.children.as_array();
            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));

            let mut of_type_id = TypeId::Node(ctx.variant_id, of.id);
            let mut of = emit_node(ctx, of);
            if let Some(type_infer::Type { kind: type_infer::TypeKind::Reference, args }) = ctx.types.get(of_type_id).kind {
                of_type_id = args.as_ref().unwrap()[0];
                let (new_reg, layout) = ctx.create_reg_and_layout(of_type_id);
                ctx.emit_dereference(new_reg, of, layout);
                of = new_reg;
            }

            let of_type = ctx.types.value_to_compiler_type(of_type_id);
            let Some(member) = of_type.member(*name) else {
                unreachable!("Type {} doesn't have member {}, but it got through the typer", of_type, *name)
            };

            debug_assert_eq!(member.indirections, 1);

            ctx.emit_move(
                to,
                get_member(of, member.byte_offset),
                to_layout,
            );
            to
        }
        NodeKind::Binary {
            op: BinaryOp::Assign,
        } => {
            let [to, from] = node.children.as_array();
            let from = emit_node(ctx, from);
            emit_declarative_lvalue(ctx, to, from, false);

            let empty_result = StackValue::ZST;
            empty_result
        }
        NodeKind::Binary { op } => {
            let [left, right] = node.children.as_array();
            let to = ctx.create_reg(TypeId::Node(ctx.variant_id, node.id));

            let a = emit_node(ctx, left);
            let b = emit_node(ctx, right);

            let type_id = TypeId::Node(ctx.variant_id, left.id);
            let type_ = ctx.types.get(type_id);
            let r_type_id = TypeId::Node(ctx.variant_id, right.id);
            let r_type = ctx.types.get(r_type_id);
            if let (type_infer::TypeKind::Reference, type_infer::TypeKind::Int) = (type_.kind(), r_type.kind()) {
                let pointee_id = type_.args()[0];
                let pointee_layout = *ctx.types.get(pointee_id).layout.unwrap();
                let b_copy = ctx.create_reg_with_layout(Layout::USIZE);
                ctx.emit_binary_imm_u64(BinaryOp::Mult, b_copy, b, pointee_layout.size as u64);
                ctx.emit_binary(*op, to, a, b_copy, PrimitiveType::U64);
            } else {
                let number_type = ctx.to_number_type(TypeId::Node(ctx.variant_id, left.id)).unwrap();
                ctx.emit_binary(*op, to, a, b, number_type);
            }

            to
        }
        NodeKind::Tuple => {
            let to = ctx.create_reg(node_type_id);

            let mut fields = StructLayout::new(0);
            for child in node.children.into_iter() {
                let child_layout = *ctx.types.get(TypeId::Node(ctx.variant_id, child.id)).layout.unwrap();
                let child_value = emit_node(ctx, child);

                let offset = fields.next(child_layout);
                ctx.emit_move(get_member(to, offset), child_value, child_layout);
            }

            to
        }
        NodeKind::ArrayLiteral => {
            let to = ctx.create_reg(node_type_id);

            let mut offset = 0;
            for child in node.children.into_iter() {
                let child_layout = *ctx.types.get(TypeId::Node(ctx.variant_id, child.id)).layout.unwrap();
                let child_value = emit_node(ctx, child);

                ctx.emit_move(get_member(to, offset), child_value, child_layout);
                offset += child_layout.size;
            }

            to
        }
        NodeKind::Reference => {
            let [operand] = node.children.as_array();
            emit_lvalue(ctx, true, operand)
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            let [operand] = node.children.as_array();
            let (to, layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            let from = emit_node(ctx, operand);
            ctx.emit_dereference(to, from, layout);
            to
        }
        NodeKind::Unary { op } => {
            let [operand] = node.children.as_array();
            let to = ctx.create_reg(TypeId::Node(ctx.variant_id, node.id));
            let from = emit_node(ctx, operand);
            let number_type = ctx.to_number_type(TypeId::Node(ctx.variant_id, operand.id)).unwrap();
            ctx.emit_unary(*op, to, from, number_type);
            to
        }
        NodeKind::Local { local_id, .. } => {
            ctx.locals.get(*local_id).value.unwrap()
        }
        NodeKind::ConstAtEvaluation { .. } => {
            // TODO: Implement this, it's not going to work yet because emission cannot produce errors,
            // and assertion failures are errors.
            todo!()
            /*let type_ = ctx.ast.get(*inner).type_();
            let constant =
                crate::interp::emit_and_run(ctx.thread_context, ctx.program, ctx.locals, &ctx.ast, *inner);
            StackValue::Global(constant, type_)*/
        }
        NodeKind::Defer => {
            let [deferring] = node.children.as_array();
            ctx.defers.push(deferring);
            StackValue::ZST
        }
        NodeKind::Block { label } => {
            let num_defers_at_start = ctx.defers.len();

            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));

            if let Some(label) = *label {
                let ir_labels = (0..=ctx.locals.get_label(label).num_defers)
                    .map(|_| ctx.create_label())
                    .collect();
                let label_ref = ctx.locals.get_label_mut(label);
                label_ref.ir_labels = Some(ir_labels);
                label_ref.value = Some(to);
            }

            let head = ctx.registers.head;

            let mut children = node.children.into_iter();
            for content in children.by_ref().take(node.children.len() - 1) {
                emit_node(ctx, content);
            }

            let from = emit_node(ctx, children.next().unwrap());
            ctx.emit_move(to, from, to_layout);

            for (i, defer_index) in (num_defers_at_start..ctx.defers.len()).enumerate().rev() {
                if let Some(label) = *label {
                    let ir_label = ctx.locals.get_label(label).ir_labels.as_ref().unwrap()[i + 1];
                    ctx.define_label(ir_label);
                }

                let defer = ctx.defers[defer_index].clone();
                emit_node(ctx, defer);
            }

            if let Some(label) = *label {
                let ir_label = ctx.locals.get_label(label).ir_labels.as_ref().unwrap()[0];
                ctx.define_label(ir_label);
            }

            ctx.defers.truncate(num_defers_at_start);

            ctx.registers.head = head;
            to
        }
        NodeKind::ResolvedGlobal(id, _) => {
            let (ptr, _) = ctx.program.get_member_value(*id);

            if let type_infer::TypeKind::Function = ctx.types.get(TypeId::Node(ctx.variant_id, node.id)).kind() {
                let function_id = unsafe { *(ptr.as_ptr() as *const FunctionId) };
                if !ctx.calling.contains(&function_id) {
                    ctx.calling.push(function_id);
                }
            }

            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_global(to, ptr, to_layout);
            to
        }
        NodeKind::FunctionCall => {
            let mut children = node.children.into_iter();
            let calling_node = children.next().unwrap();

            let (to, to_layout) = ctx.create_reg_and_typed_layout(TypeId::Node(ctx.variant_id, node.id));
            let calling = emit_node(ctx, calling_node.clone());
            let calling_type = ctx.types.get(TypeId::Node(ctx.variant_id, calling_node.id));
            // @Performance
            let output_args = calling_type.args().to_vec().into_iter().skip(1).map(|v| {
                ctx.create_reg_and_typed_layout(v)
            }).collect::<Vec<_>>();

            if let Some(AdditionalInfoKind::FunctionCall(args)) = ctx.additional_info.get(&(ctx.variant_id, node.id)) {
                debug_assert_eq!(args.len(), children.len());
                for (arg, node) in args.iter().zip(children) {
                    match *arg {
                        FunctionArgUsage::ValueOfAssign { function_arg } => {
                            let [_, right] = node.children.into_array();
                            let given = emit_node(ctx, right);

                            let (to, to_layout) = output_args[function_arg];
                            ctx.emit_move(to, given, to_layout.layout);
                        }
                        FunctionArgUsage::Value { function_arg } => {
                            let given = emit_node(ctx, node);

                            let (to, to_layout) = output_args[function_arg];
                            ctx.emit_move(to, given, to_layout.layout);
                        }
                        FunctionArgUsage::TupleElement { function_arg, field } => {
                            let given = emit_node(ctx, node);

                            let calling_type = ctx.types.get(TypeId::Node(ctx.variant_id, calling_node.id));
                            let arg_type_id = calling_type.args()[function_arg + 1];
                            let (_, offset, arg_type_) = ctx.types.value_to_compiler_type(arg_type_id).0.members[field];
                            let to_layout = Layout { size: arg_type_.size(), align: arg_type_.align() };

                            let (to, _) = output_args[function_arg];
                            ctx.emit_move(get_member(to, offset), given, to_layout);
                        }
                    }
                }
            } else {
                for (&(to, to_layout), node) in output_args.iter().zip(children) {
                    let given = emit_node(ctx, node);
                    ctx.emit_move(to, given, to_layout.layout);
                }
            }

            ctx.emit_call((to, to_layout), calling, output_args, calling_node.loc);

            to
        }
        NodeKind::TypeBound { .. } => {
            let [value, _] = node.children.as_array();
            emit_node(ctx, value)
        }
        NodeKind::Parenthesis | NodeKind::Explain => {
            let [value] = node.children.as_array();
            emit_node(ctx, value)
        }
        NodeKind::SizeOf => {
            let [inner] = node.children.as_array();
            let inner_type = TypeId::Node(ctx.variant_id, inner.id);
            let size = ctx.types.get(inner_type).layout.unwrap().size;

            let to = ctx.create_reg(node_type_id);
            ctx.emit_move_imm(to, size.to_le_bytes(), Layout::USIZE);
            to
        }
        NodeKind::TypeAsValue => {
            let [inner] = node.children.as_array();
            let inner_type = TypeId::Node(ctx.variant_id, inner.id);
            let compiler_type = ctx.types.value_to_compiler_type(inner_type);
            let constant_ref = ctx.program.insert_buffer(Type::new(TypeKind::Type), &compiler_type as *const _ as *const u8);

            let (to, to_layout) = ctx.create_reg_and_layout(node_type_id);
            ctx.emit_global(to, constant_ref, to_layout);
            to
        }
        NodeKind::PolymorphicArgument(_) => {
            let &AdditionalInfoKind::Constant(constant) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };
            let inner_type = TypeId::Node(ctx.variant_id, node.id);
            let (to, to_layout) = ctx.create_reg_and_layout(inner_type);
            ctx.emit_global(to, constant, to_layout);
            to
        }
        NodeKind::If {
            is_const: Some(_),
        } => {
            let [_, true_body, false_body] = node.children.as_array();

            let &AdditionalInfoKind::ConstIfResult(result) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };
            if result {
                emit_node(ctx, true_body)
            } else {
                emit_node(ctx, false_body)
            }
        }
        NodeKind::PolymorphicArgs { .. } | NodeKind::Global { .. } => {
            let &AdditionalInfoKind::Monomorphised(id) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };

            let (ptr, _) = ctx.program.get_member_value(id);

            if let type_infer::TypeKind::Function = ctx.types.get(TypeId::Node(ctx.variant_id, node.id)).kind() {
                let function_id = unsafe { *(ptr.as_ptr() as *const FunctionId) };
                if !ctx.calling.contains(&function_id) {
                    ctx.calling.push(function_id);
                }
            }

            let (to, to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_global(to, ptr, to_layout);
            to
        }
        NodeKind::BuiltinFunction(_) | NodeKind::FunctionDeclaration { .. } => {
            let &AdditionalInfoKind::Function(id) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };

            let inner_type = TypeId::Node(ctx.variant_id, node.id);
            let compiler_type = ctx.types.value_to_compiler_type(inner_type);
            let constant_ref = ctx.program.insert_buffer(compiler_type, &id as *const _ as *const u8);

            let (to, to_layout) = ctx.create_reg_and_layout(inner_type);
            ctx.emit_global(to, constant_ref, to_layout);
            to
        }
        NodeKind::Is => {
            let to = ctx.create_reg(node_type_id);
           
            let &AdditionalInfoKind::IsExpression(comparison_id) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };
            let value = ctx.types.get_comparison_result(comparison_id);
            ctx.emit_move_imm(to, (value as u64).to_le_bytes(), Layout::BOOL);
            to
        }
        c => unreachable!("This node should not reach emission: {:?}", c),
    }
}

fn emit_declarative_lvalue<'a>(
    ctx: &mut Context<'a, '_>,
    mut node: NodeView<'a>,
    from: StackValue,
    is_declaring: bool,
) {
    ctx.emit_debug(node.loc);
    let node_type_id = TypeId::Node(ctx.variant_id, node.id);

    match &node.kind {
        NodeKind::Member { .. } => {
            debug_assert!(!is_declaring);

            let to = emit_lvalue(ctx, false, node);
            let layout = *ctx.types.get(node_type_id).layout.unwrap();
            ctx.emit_indirect_move(to, from, layout);
        }
        NodeKind::Binary { op: BinaryOp::BitAnd } => {
            let [left, right] = node.children.into_array();

            emit_declarative_lvalue(ctx, left, from, is_declaring);
            emit_declarative_lvalue(ctx, right, from, is_declaring);
        }
        NodeKind::ImplicitType => {}
        NodeKind::Declare => {
            let [value] = node.children.as_array();
            emit_declarative_lvalue(ctx, value, from, true);
        }
        NodeKind::Tuple => {
            let mut temp = Vec::with_capacity(node.children.len());
            let mut child_layouting = StructLayout::new(0);
            for child in node.children.into_iter() {
                let (to, child_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, child.id));
                let offset = child_layouting.next(child_layout);
                ctx.emit_move(to, get_member(from, offset), child_layout);
                temp.push(to);
            }

            for (child, to) in node.children.into_iter().zip(temp) {
                emit_declarative_lvalue(ctx, child, to, is_declaring);
            }
        }
        NodeKind::ArrayLiteral => {
            let mut temp = Vec::with_capacity(node.children.len());
            let mut offset = 0;
            for child in node.children.into_iter() {
                let (to, child_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, child.id));
                ctx.emit_move(to, get_member(from, offset), child_layout);
                offset += child_layout.size;
                temp.push(to);
            }

            for (child, to) in node.children.into_iter().zip(temp) {
                emit_declarative_lvalue(ctx, child, to, is_declaring);
            }
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            debug_assert!(!is_declaring);
            let [operand] = node.children.as_array();
            let pointer = emit_node(ctx, operand);
            let layout = *ctx.types.get(node_type_id).layout.unwrap();
            ctx.emit_indirect_move(pointer, from, layout);
        }
        NodeKind::Local { local_id, .. } => {
            if is_declaring {
                let local = ctx.locals.get(*local_id);
                let type_id = TypeId::Node(ctx.variant_id, local.declared_at.unwrap());
                let (local_value, local_value_layout) = ctx.create_reg_and_layout(type_id);
                let local = ctx.locals.get_mut(*local_id);
                local.value = Some(local_value);
                ctx.emit_move(local_value, from, local_value_layout);
            } else {
                let to = ctx.locals.get(*local_id).value.unwrap();
                let layout = *ctx.types.get(node_type_id).layout.unwrap();
                ctx.emit_move(to, from, layout);
            }
        }
        NodeKind::Parenthesis => {
            let [value] = node.children.as_array();
            emit_declarative_lvalue(ctx, value, from, is_declaring);
        }
        NodeKind::TypeBound => {
            let [value, _] = node.children.as_array();
            emit_declarative_lvalue(ctx, value, from, is_declaring);
        }
        kind => {
            unreachable!(
                "{:?} is not an lvalue. This is just something I haven't implemented checking for in the compiler yet",
                kind
            )
        }
    }
}

fn emit_lvalue<'a>(
    ctx: &mut Context<'a, '_>,
    can_reference_temporaries: bool,
    mut node: NodeView<'a>,
) -> StackValue {
    ctx.emit_debug(node.loc);

    // @TODO: Creating all these types suck, maybe we should remove the damn `Global` thing from registers,
    // and instead let them just be pointers to values? These pointers wouldn't even be considered pointers from
    // the language, but just registers that need to point to things.
    let ref_type_id = ctx.types.add_type(type_infer::TypeKind::Reference, Args([(TypeId::Node(ctx.variant_id, node.id), Reason::temp_zero())]), ());

    match &node.kind {
        NodeKind::Member { name } => {
            let [of] = node.children.as_array();

            // If `of` is a reference, we need to do stuff.
            let (base_type, parent_value) = if let Some(type_infer::Type { kind: type_infer::TypeKind::Reference, args }) = ctx.types.get(TypeId::Node(ctx.variant_id, of.id)).kind {
                let arg = args.as_ref().unwrap()[0];
                (ctx.types.value_to_compiler_type(arg), emit_node(ctx, of))
            } else {
                let parent_value = emit_lvalue(ctx, can_reference_temporaries, of.clone());
                (ctx.types.value_to_compiler_type(TypeId::Node(ctx.variant_id, of.id)), parent_value)
            };

            let member = base_type.member(*name).expect("This should have already been made sure to exist in the typer");

            let to = ctx.create_reg(ref_type_id);

            ctx.emit_binary_imm_u64(BinaryOp::Add, to, parent_value, member.byte_offset as u64);
            to
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            let [operand] = node.children.as_array();
            emit_node(ctx, operand)
        }
        NodeKind::Local { local_id, .. } => {
            let to = ctx.create_reg(ref_type_id);
            let from = ctx.locals.get(*local_id).value.unwrap();
            ctx.emit_reference(to, from);
            to
        }
        NodeKind::ResolvedGlobal(id, _) => {
            let to = ctx.create_reg(ref_type_id);
            let (from_ref, from_type) = ctx.program.get_member_value(*id);
            ctx.emit_ref_to_global(to, from_ref, from_type);
            to
        }
        NodeKind::Parenthesis => {
            let [value] = node.children.as_array();
            emit_lvalue(ctx, can_reference_temporaries, value)
        }
        NodeKind::TypeBound => {
            let [value, _] = node.children.as_array();
            emit_lvalue(ctx, can_reference_temporaries, value)
        }
        kind => {
            if can_reference_temporaries {
                let to = ctx.create_reg(ref_type_id);
                let from = emit_node(ctx, node);
                ctx.emit_reference(to, from);
                to
            } else {
                unreachable!(
                    "{:?} is not an lvalue. This is just something I haven't implemented checking for in the compiler yet",
                    kind
                )
            }
        }
    }
}

enum Value {
    Immediate([u8; 8]),
    Constant {
        constant: ConstantRef,
        offset: usize,
    },
    Stack(StackValue),
    RefInStack {
        value: StackValue,
        offset: usize,
    },
}

pub struct Context<'a, 'b> {
    pub thread_context: &'a mut ThreadContext<'b>,
    pub instr: Vec<Instr>,
    pub registers: StackAllocator,
    pub locals: &'a mut LocalVariables,
    pub program: &'b Program,
    pub types: &'a mut TypeSystem,
    pub label_locations: Vec<usize>,
    pub calling: Vec<FunctionId>,
    pub last_location: Option<Location>,
    pub variant_id: AstVariantId,
    pub additional_info: &'a AdditionalInfo,

    pub defers: Vec<NodeView<'a>>,
}

impl Context<'_, '_> {
    pub fn emit_debug(&mut self, loc: Location) {
        if self.program.arguments.debug {
            if let Some(last_location) = self.last_location {
                if last_location.file == loc.file && last_location.line == loc.line {
                    return;
                }
            }

            self.instr.push(Instr::DebugLocation(loc));
        }
    }

    fn flush_value(&mut self, from: Value, layout: Layout) -> StackValue {
        let temp = self.create_reg_with_layout(layout);
        self.flush_value_to(temp, from, layout);
        temp
    }

    fn flush_value_to(&mut self, to: StackValue, from: Value, layout: Layout) {
        if layout.size == 0 { return; }

        match from {
            Value::Immediate(num) => {
                self.emit_move_imm(to, num, layout);
            }
            Value::Constant { constant, offset } => {
                // TODO: This can be done more efficiently if RefGlobal allows an offset.
                let temp = self.create_reg_with_layout(Layout::PTR);
                self.instr.push(Instr::RefGlobal { to_ptr: temp, global: constant });
                self.emit_binary_imm_u64(BinaryOp::Add, temp, temp, offset as u64);
                self.emit_dereference(to, temp, layout);
            }
            Value::Stack(value) => {
                self.emit_move(to, value, layout);
            }
            Value::RefInStack { value, offset } => {
                if offset == 0 {
                    self.emit_dereference(to, value, layout);
                } else {
                    // TODO: This can be done more efficiently if Dereference allows an offset.
                    let temp = self.create_reg_with_layout(Layout::PTR);
                    self.emit_move(temp, value, Layout::PTR);
                    self.emit_binary_imm_u64(BinaryOp::Add, temp, temp, offset as u64);
                    self.emit_dereference(to, temp, layout);
                }
            }
        }
    }

    fn create_reg_and_typed_layout(&mut self, type_id: TypeId) -> (StackValue, TypedLayout) {
        let number_type = self.to_number_type(type_id);

        let type_ = self.types.get(type_id);
        let layout = *type_.layout.unwrap();

        (
            self.create_reg_with_layout(layout),
            TypedLayout {
                primitive: number_type,
                layout,
            },
        )
    }

    fn create_reg_and_layout(&mut self, type_id: TypeId) -> (StackValue, Layout) {
        let layout = *self.types.get(type_id).layout.unwrap();

        (
            self.create_reg_with_layout(layout),
            layout
        )
    }

    fn create_reg(&mut self, type_id: TypeId) -> StackValue {
        self.create_reg_and_layout(type_id).0
    }

    fn create_reg_with_layout(&mut self, layout: Layout) -> StackValue {
        debug_assert!(layout.align > 0, "Incomplete layout");

        if layout.size == 0 {
            StackValue::ZST
        } else {
            self.registers.create(layout.align, layout.size)
        }
    }

    fn create_label(&mut self) -> LabelId {
        let id = LabelId(self.label_locations.len());
        self.label_locations.push(0xffff_ffff);
        id
    }

    fn define_label(&mut self, label_id: LabelId) {
        self.label_locations[label_id.0] = self.instr.len();
        self.instr.push(Instr::LabelDefinition(label_id));
    }

    fn emit_global(&mut self, to: StackValue, global: ConstantRef, layout: Layout) {
        if layout.size != 0 {
            let temp = self.create_reg_with_layout(Layout::PTR);
            self.instr.push(Instr::RefGlobal { to_ptr: temp, global });
            self.instr.push(Instr::Dereference { to, from_ptr: temp, size: layout.size });
        }
    }

    fn emit_ref_to_global(&mut self, to_ptr: StackValue, global: ConstantRef, type_: crate::types::Type) {
        if type_.size() != 0 {
            println!("{}", crate::program::constant_to_str(type_, global, 0));
            self.instr.push(Instr::RefGlobal { to_ptr, global });
        }
    }

    fn emit_jump_if_zero(&mut self, condition: StackValue, to: LabelId) {
        self.instr.push(Instr::JumpIfZero { condition, to });
    }

    fn emit_jump(&mut self, to: LabelId) {
        self.instr.push(Instr::Jump { to });
    }

    fn emit_set_to_zero(&mut self, to_ptr: StackValue, layout: Layout) {
        self.instr.push(Instr::SetToZero { to_ptr, size: layout.size });
    }

    fn emit_convert_num(&mut self, to: StackValue, to_number: PrimitiveType, from: StackValue, from_number: PrimitiveType) {
        self.instr.push(Instr::ConvertNum { to, to_number, from, from_number });
    }

    fn emit_member(&mut self, to: StackValue, of: StackValue, member_offset: usize, size: usize) {
        if size != 0 {
            let member = StackValue(of.0 + member_offset);
            self.instr.push(Instr::Move { to, from: member, size });
        }
    }

    fn emit_reference(&mut self, to: StackValue, from: StackValue) {
        self.instr.push(Instr::StackPtr { to, take_pointer_to: from });
    }

    fn emit_dereference(&mut self, to: StackValue, from_ptr: StackValue, layout: Layout) {
        if layout.size != 0 {
            self.instr.push(Instr::Dereference { to, from_ptr, size: layout.size });
        }
    }

    fn emit_move_imm(&mut self, to: StackValue, from: [u8; 8], layout: Layout) {
        if layout.size != 0 {
            self.instr.push(Instr::MoveImm {
                to,
                from,
                size: layout.size,
            });
        }
    }

    fn emit_move(&mut self, to: StackValue, from: StackValue, layout: Layout) {
        if layout.size != 0 {
            self.instr.push(Instr::Move {
                to,
                from,
                size: layout.size,
            });
        }
    }

    fn emit_indirect_move(&mut self, to_ptr: StackValue, from: StackValue, layout: Layout) {
        if layout.size != 0 {
            self.instr.push(Instr::IndirectMove {
                to_ptr,
                from,
                size: layout.size,
            });
        }
    }

    fn emit_call(&mut self, to: (StackValue, TypedLayout), pointer: StackValue, args: Vec<(StackValue, TypedLayout)>, loc: Location) {
        self.instr.push(Instr::Call { to, pointer, args, loc });
    }

    fn emit_unary(&mut self, op: UnaryOp, to: StackValue, from: StackValue, type_: PrimitiveType) {
        self.instr.push(Instr::Unary { op, to, from, type_ });
    }

    fn emit_binary_imm_u64(&mut self, op: BinaryOp, to: StackValue, a: StackValue, b: u64) {
        self.instr.push(Instr::BinaryImm { to, a, b, op, type_: PrimitiveType::U64 });
    }

    fn emit_binary(&mut self, op: BinaryOp, to: StackValue, a: StackValue, b: StackValue, type_: PrimitiveType) {
        self.instr.push(Instr::Binary { to, a, b, op, type_ });
    }

    fn emit_incr_ptr(&mut self, to: StackValue, amount: StackValue, scale: usize) {
        self.instr.push(Instr::IncrPtr { to, amount, scale });
    }

    fn to_typed_layout(&self, type_id: TypeId) -> TypedLayout {
        let layout = *self.types.get(type_id).layout.unwrap();
        let primitive = self.to_number_type(type_id);

        TypedLayout {
            layout,
            primitive,
        }
    }

    fn to_number_type(&self, type_id: TypeId) -> Option<PrimitiveType> {
        let type_ = self.types.get(type_id);
        match type_.kind() {
            type_infer::TypeKind::Int => {
                let Some(&type_infer::Type { kind: type_infer::TypeKind::IntSigned(signed), .. }) = self.types.get(type_.args()[0]).kind else { panic!() };
                let Some(&type_infer::Type { kind: type_infer::TypeKind::IntSize(size), .. }) = self.types.get(type_.args()[1]).kind else { panic!() };

                Some(match (signed, size) {
                    (true, 0) => PrimitiveType::I64,
                    (true, 1) => PrimitiveType::I8,
                    (true, 2) => PrimitiveType::I16,
                    (true, 4) => PrimitiveType::I32,
                    (true, 8) => PrimitiveType::I64,
                    (false, 0) => PrimitiveType::U64,
                    (false, 1) => PrimitiveType::U8,
                    (false, 2) => PrimitiveType::U16,
                    (false, 4) => PrimitiveType::U32,
                    (false, 8) => PrimitiveType::U64,
                    _ => unreachable!(),
                })
            }
            type_infer::TypeKind::Float => {
                let Some(&type_infer::Type { kind: type_infer::TypeKind::IntSize(size), .. }) = self.types.get(type_.args()[0]).kind else { panic!() };

                Some(match size {
                    4 => PrimitiveType::F32,
                    8 => PrimitiveType::F64,
                    _ => unreachable!(),
                })
            }
            type_infer::TypeKind::Reference => {
                Some(PrimitiveType::U64)
            }
            type_infer::TypeKind::Bool => {
                Some(PrimitiveType::Bool)
            }
            _ => None,
        }
    }
}

fn get_member(value: StackValue, offset: usize) -> StackValue {
    StackValue(value.0 + offset)
}
