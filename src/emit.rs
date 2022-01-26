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
    emit_inner_function_declarations: bool,
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
        emit_inner_function_declarations,

        defers: Vec::new(),
    };

    let (result, result_layout) = emit_node(&mut ctx, ast.get(node));

    let result = ctx.flush_value(&result, result_layout);

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
    node: NodeView<'_>,
    additional_info: &AdditionalInfo,
    node_id: NodeId,
    variant_id: AstVariantId,
    loc: Location,
    function_id: FunctionId,
    emit_inner_function_declarations: bool,
) {
    // If it's already there, don't emit it.
    if program.get_routine(function_id).is_some() {
        return;
    }

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
        emit_inner_function_declarations,
    };

    let function_type = ctx.types.get(TypeId::Node(ctx.variant_id, node_id));
    let args = function_type.args();

    debug_assert_eq!(function_type.kind(), &type_infer::TypeKind::Function);

    // Pretend there are actual values on the stack
    // @Performance
    let args: Vec<_> = args.to_vec().into_iter().skip(1).map(|v| {
        ctx.create_reg_and_typed_layout(v)
    }).collect();

    let mut children = node.children.into_iter();
    for &(passed_as, _) in args.iter() {
        let child = children.next().unwrap();
        emit_declarative_lvalue(&mut ctx, child, &Value::Stack(passed_as), true);
    }

    // Now that we've read all the arguments of the function, only the return type,
    // and the body are left. We don't need the return type, as that is only for the typer,
    // so we skip that one.

    let body = children.nth(1).unwrap();
    let (result, result_layout) = emit_node(&mut ctx, body);

    let result = ctx.flush_value(&result, result_layout);

    let routine = Routine::UserDefined(UserDefinedRoutine {
        loc,
        name: "temp".into(),
        label_locations: ctx.label_locations,
        instr: ctx.instr,
        stack: ctx.registers,
        args,
        result,
        result_layout,
    });

    if ctx.program.set_routine_of_function(function_id, ctx.calling, routine) {
        let routine = ctx.program.get_routine(function_id);
        ctx.thread_context.emitters.emit_routine(ctx.program, function_id, &routine.unwrap());
    }
}

fn emit_node<'a>(ctx: &mut Context<'a, '_>, mut node: NodeView<'a>) -> (Value, TypedLayout) {
    ctx.emit_debug(node.loc);

    let node_type_id = TypeId::Node(ctx.variant_id, node.id);

    match &node.kind {
        NodeKind::Empty => (Value::ZST, TypedLayout::ZST),
        NodeKind::Break {
            label: label_id,
            num_defer_deduplications,
        } => {
            let [value] = node.children.as_array();
            
            let label = ctx.locals.get_label(*label_id);
            let ir_label = label.ir_labels.as_ref().unwrap()[*num_defer_deduplications];
            let label_value = label.value.unwrap();

            let (from, from_layout) = emit_node(ctx, value);
            let from = ctx.flush_value(&from, from_layout);

            for defer_index in (ctx.locals.get_label(*label_id).defer_depth
                + *num_defer_deduplications..ctx.defers.len())
                .rev()
            {
                emit_node(ctx, ctx.defers[defer_index].clone());
            }

            ctx.emit_move(label_value, from, from_layout.layout);
            ctx.emit_jump(ir_label);

            (Value::ZST, TypedLayout::ZST)
        }
        NodeKind::For {
            is_const: Some(_),
            label,
        } => {
            let [iterating, i_value_decl, mut inner, else_body] = node.children.as_array();

            let &AdditionalInfoKind::ConstForAstVariants { referenced, ref variant_ids } = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };

            let end_label = ctx.create_label();

            let (to, _to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            let label = ctx.locals.get_label_mut(*label);
            label.value = Some(to);
            label.ir_labels = Some(vec![end_label]);

            // Set up iterator values
            let i_value = ctx.create_reg(TypeId::Node(ctx.variant_id, i_value_decl.id));
            ctx.emit_move_imm(i_value, 0_usize.to_le_bytes(), Layout::USIZE);

            // TODO: Figure out how to abstract this.
            if referenced {
                let (iterating_value_ptr, iterating_value_ptr_layout) = emit_node(ctx, iterating.clone());
                let iterating_value_ptr = ctx.flush_value(&iterating_value_ptr, iterating_value_ptr_layout);

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

                    emit_declarative_lvalue(ctx, i_value_decl.clone(), &Value::Stack(i_value), true);

                    let old_variant_id = ctx.variant_id;
                    ctx.variant_id = variant_id;
                    emit_declarative_lvalue(ctx, v_value_decl, &Value::Stack(iterating_value_ptr), true);
                    emit_node(ctx, body);
                    ctx.variant_id = old_variant_id;

                    ctx.emit_binary_imm_u64(BinaryOp::Add, i_value, i_value, 1);
                }
            } else {
                let (iterating_value, iterating_value_layout) = emit_node(ctx, iterating.clone());
                let iterating_value = ctx.flush_value(&iterating_value, iterating_value_layout);

                let mut iterating_value_fields = StructLayout::new(0);
                for &variant_id in variant_ids.iter() {
                    emit_declarative_lvalue(ctx, i_value_decl.clone(), &Value::Stack(i_value), true);

                    let [v_value_decl, body] = inner.children.as_array();

                    let field_layout = *ctx.types.get(TypeId::Node(variant_id, v_value_decl.id)).layout.unwrap();
                    let field_offset = iterating_value_fields.next(field_layout);

                    let old_variant_id = ctx.variant_id;
                    ctx.variant_id = variant_id;
                    emit_declarative_lvalue(ctx, v_value_decl, &Value::Stack(get_member(iterating_value, field_offset)), true);
                    emit_node(ctx, body);
                    ctx.variant_id = old_variant_id;

                    ctx.emit_binary_imm_u64(BinaryOp::Add, i_value, i_value, 1);
                }
            }

            let (evaluate_to, evaluate_to_layout) = emit_node(ctx, else_body);
            ctx.flush_value_to(to, &evaluate_to, evaluate_to_layout);
            ctx.define_label(end_label);
            (Value::Stack(to), evaluate_to_layout)
        }
        NodeKind::For {
            is_const: None,
            label,
        } => {
            let [iterating, i_value_decl, mut inner, else_body] = node.children.as_array();
            let [v_value_decl, body] = inner.children.as_array();

            let end_label = ctx.create_label();
            let (to, _to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            ctx.locals.get_label_mut(*label).value = Some(to);
            ctx.locals.get_label_mut(*label).ir_labels = Some(vec![end_label]);

            let (iterating_value, iterating_value_layout) = emit_node(ctx, iterating.clone());
            let mut iterating_value = ctx.flush_value(&iterating_value, iterating_value_layout);

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

            emit_declarative_lvalue(ctx, i_value_decl, &Value::Stack(i_value), true);

            if by_value {
                let (temp, layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, v_value_decl.id));
                ctx.emit_dereference(temp, current, layout);
                emit_declarative_lvalue(ctx, v_value_decl, &Value::Stack(temp), true);
            } else {
                emit_declarative_lvalue(ctx, v_value_decl, &Value::Stack(current), true);
            }
            emit_node(ctx, body);

            ctx.emit_binary_imm_u64(BinaryOp::Add, current, current, pointee_layout.size as u64);
            ctx.emit_binary_imm_u64(BinaryOp::Add, i_value, i_value, 1);

            ctx.emit_jump(condition_label);

            ctx.define_label(else_body_label);

            let (else_body_from, else_body_from_layout) = emit_node(ctx, else_body);
            ctx.flush_value_to(to, &else_body_from, else_body_from_layout);

            ctx.define_label(end_label);

            (Value::Stack(to), else_body_from_layout)
        }
        NodeKind::While {
            label,
        } => {
            let [i_value_decl, condition, body, else_body] = node.children.as_array();

            let end_label = ctx.create_label();
            let else_body_label = ctx.create_label();

            let (to, _to_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, node.id));
            let label = ctx.locals.get_label_mut(*label);
            label.value = Some(to);
            label.ir_labels = Some(vec![end_label]);

            let i_value = ctx.create_reg(TypeId::Node(ctx.variant_id, i_value_decl.id)); 
            ctx.emit_move_imm(i_value, 0_usize.to_le_bytes(), Layout::USIZE);

            // Condition
            let condition_label = ctx.create_label();
            ctx.define_label(condition_label);

            emit_declarative_lvalue(ctx, i_value_decl, &Value::Stack(i_value), true);

            let (condition, condition_layout) = emit_node(ctx, condition);
            let condition = ctx.flush_value(&condition, condition_layout);
            ctx.emit_jump_if_zero(condition, else_body_label);

            // Loop body
            emit_node(ctx, body);
            ctx.emit_binary_imm_u64(BinaryOp::Add, i_value, i_value, 1);
            ctx.emit_jump(condition_label);

            // Else body
            ctx.define_label(else_body_label);

            let (else_body_value, else_body_layout) = emit_node(ctx, else_body);
            ctx.flush_value_to(to, &else_body_value, else_body_layout);

            // End
            ctx.define_label(end_label);

            (Value::Stack(to), else_body_layout)
        }
        NodeKind::If {
            is_const: None,
        } => {
            let [condition, true_body, false_body] = node.children.as_array();

            let (condition, condition_layout) = emit_node(ctx, condition);
            let condition = ctx.flush_value(&condition, condition_layout);

            let start_of_false_body = ctx.create_label();
            let end_of_false_body = ctx.create_label();

            ctx.emit_jump_if_zero(condition, start_of_false_body);

            let to = ctx.create_reg(TypeId::Node(ctx.variant_id, node.id));

            // True body
            let (true_body, true_body_layout) = emit_node(ctx, true_body);
            ctx.flush_value_to(to, &true_body, true_body_layout);
            ctx.emit_jump(end_of_false_body);

            // False body
            ctx.define_label(start_of_false_body);
            let (false_body, false_body_layout) = emit_node(ctx, false_body);
            ctx.flush_value_to(to, &false_body, false_body_layout);

            ctx.define_label(end_of_false_body);

            (Value::Stack(to), false_body_layout)
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

            let (to, to_layout) = ctx.create_reg_and_typed_layout(TypeId::Node(ctx.variant_id, node.id));
            ctx.emit_global(to, ptr, to_layout.layout);
            (Value::Stack(to), to_layout)
        }
        NodeKind::Literal(Literal::Int(num)) => {
            let to_layout = ctx.get_typed_layout(TypeId::Node(ctx.variant_id, node.id));
            (Value::Immediate((*num as u64).to_le_bytes()), to_layout)
        }
        &NodeKind::Literal(Literal::Float(num)) => {
            let to_layout = ctx.get_typed_layout(TypeId::Node(ctx.variant_id, node.id));

            let bytes = match to_layout.size {
                4 => {
                    ((num as f32).to_bits() as u64).to_le_bytes()
                }
                8 => {
                    num.to_bits().to_le_bytes()
                }
                _ => unreachable!(),
            };

            (Value::Immediate(bytes), to_layout)
        }
        NodeKind::Zeroed => {
            let to_layout = ctx.get_typed_layout(TypeId::Node(ctx.variant_id, node.id));
            (Value::Zeroed, to_layout)
        }
        NodeKind::Uninit => {
            let to_layout = ctx.get_typed_layout(TypeId::Node(ctx.variant_id, node.id));
            (Value::Uninit, to_layout)
        }
        NodeKind::Cast => {
            let [value] = node.children.as_array();
            let (from, from_layout) = emit_node(ctx, value.clone());
            let from = ctx.flush_value(&from, from_layout);
            let (to, to_layout) = ctx.create_reg_and_typed_layout(TypeId::Node(ctx.variant_id, node.id));

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
                (
                    Some(type_infer::Type { kind: type_infer::TypeKind::Enum { .. }, .. }),
                    Some(type_infer::Type { kind: type_infer::TypeKind::Int, .. }),
                ) => {
                    ctx.emit_move(to, from, Layout::PTR);
                }
                (
                    Some(type_infer::Type { kind: type_infer::TypeKind::Int, .. }),
                    Some(type_infer::Type { kind: type_infer::TypeKind::Enum { .. }, .. }),
                ) => {
                    ctx.emit_move(to, from, Layout::PTR);
                }
                _ => unreachable!("Internal error: Invalid types for cast reached emission"),
            }

            (Value::Stack(to), to_layout)
        }
        NodeKind::BitCast | NodeKind::Pack | NodeKind::Unpack => {
            let [value] = node.children.as_array();
            // TODO: This may not always be correct, if the typed layout doesn't match.
            emit_node(ctx, value)
        }
        NodeKind::Constant(bytes, _) => {
            if let type_infer::TypeKind::Function { .. } = ctx.types.get(TypeId::Node(ctx.variant_id, node.id)).kind() {
                let function_id = unsafe { *(bytes.as_ptr() as *const FunctionId) };
                if !ctx.calling.contains(&function_id) {
                    ctx.calling.push(function_id);
                }
            }

            let to_layout = ctx.get_typed_layout(TypeId::Node(ctx.variant_id, node.id));
            (Value::Constant { constant: *bytes, offset: 0 }, to_layout)
        }
        NodeKind::Member { name } => {
            // TODO: This can be optimized heavily using the value system.

            let [of] = node.children.as_array();

            let mut of_type_id = TypeId::Node(ctx.variant_id, of.id);
            let (mut of, mut of_layout) = emit_node(ctx, of);

            loop {
                match ctx.types.get(of_type_id).kind.as_ref().unwrap() {
                    type_infer::Type { kind: type_infer::TypeKind::Reference, args } => {
                        of_type_id = args.as_ref().unwrap()[0];

                        let old_value = ctx.flush_value(&of, of_layout);
                        of_layout = ctx.get_typed_layout(of_type_id);
                        let new_of = ctx.create_reg_with_layout(of_layout.layout);
                        ctx.emit_dereference(new_of, old_value, of_layout.layout);
                        of = Value::Stack(new_of);

                        /*let new_of = ctx.flush_value(&of, of_layout);
                        of_layout = ctx.get_typed_layout(of_type_id);
                        of = Value::PointerInStack {
                            stack_value: new_of,
                            offset: 0,
                        };*/
                    }
                    type_infer::Type { kind: type_infer::TypeKind::Unique(_) | type_infer::TypeKind::Enum { .. }, args } => {
                        of_type_id = args.as_ref().unwrap()[0];
                    }
                    _ => break,
                }
            }

            let member = ctx.types.get_member_by_name(of_type_id, *name).unwrap();

            let member = ctx.get_member_of_value(&of, of_layout, member.index, member.offset);
            let layout = ctx.get_typed_layout(node_type_id);

            (member, layout)
        }
        NodeKind::Binary {
            op: BinaryOp::Assign,
        } => {
            // TODO: This can also be improved once emit_declarative_lvalue takes a value
            let [to, from] = node.children.as_array();
            let (from, _from_layout) = emit_node(ctx, from);
            emit_declarative_lvalue(ctx, to, &from, false);

            (Value::ZST, TypedLayout::ZST)
        }
        NodeKind::Binary { op } => {
            let [left, right] = node.children.as_array();
            let (to, to_layout) = ctx.create_reg_and_typed_layout(TypeId::Node(ctx.variant_id, node.id));

            // TODO: We can improve the emission for immediate values
            let (a, a_layout) = emit_node(ctx, left);
            let a = ctx.flush_value(&a, a_layout);
            let (b, b_layout) = emit_node(ctx, right);
            let b = ctx.flush_value(&b, b_layout);

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

            (Value::Stack(to), to_layout)
        }
        NodeKind::Tuple => {
            let to_layout = ctx.get_typed_layout(node_type_id);

            let mut nodes = Vec::new();
            for child in node.children.into_iter() {
                let (child_value, child_value_layout) = emit_node(ctx, child);
                nodes.push((child_value, child_value_layout));
            }

            (Value::Tuple(nodes), to_layout)
        }
        NodeKind::ArrayLiteral => {
            // TODO: We want a `Value` that is just an array, to allow destructuring to be very fast later on.

            let (to, to_layout) = ctx.create_reg_and_typed_layout(node_type_id);

            let mut offset = 0;
            for child in node.children.into_iter() {
                let child_layout = *ctx.types.get(TypeId::Node(ctx.variant_id, child.id)).layout.unwrap();
                let (child_value, child_value_layout) = emit_node(ctx, child);
                let child_value = ctx.flush_value(&child_value, child_value_layout);

                ctx.emit_move(get_member(to, offset), child_value, child_layout);
                offset += child_layout.size;
            }

            (Value::Stack(to), to_layout)
        }
        NodeKind::Reference => {
            let [operand] = node.children.as_array();
            let to_layout = ctx.get_typed_layout(node_type_id);
            let lvalue = emit_lvalue(ctx, true, operand);
            (ctx.lvalue_as_value(&lvalue), to_layout)
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            let [operand] = node.children.as_array();
            let (to, layout) = ctx.create_reg_and_typed_layout(TypeId::Node(ctx.variant_id, node.id));
            let (from, from_layout) = emit_node(ctx, operand);
            let from = ctx.flush_value(&from, from_layout);
            ctx.emit_dereference(to, from, layout.layout);
            (Value::Stack(to), layout)
        }
        NodeKind::Unary { op } => {
            let [operand] = node.children.as_array();
            let (to, to_layout) = ctx.create_reg_and_typed_layout(TypeId::Node(ctx.variant_id, node.id));
            let (from, from_layout) = emit_node(ctx, operand);
            let from = ctx.flush_value(&from, from_layout);
            let number_type = ctx.to_number_type(TypeId::Node(ctx.variant_id, operand.id)).unwrap();
            ctx.emit_unary(*op, to, from, number_type);
            (Value::Stack(to), to_layout)
        }
        NodeKind::Local { local_id, .. } => {
            let local = ctx.locals.get(*local_id);
            let defined_at = local.declared_at.unwrap();
            let value = local.value.unwrap();
            let layout = ctx.get_typed_layout(TypeId::Node(ctx.variant_id, defined_at));
            (Value::Stack(value), layout)
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
            (Value::ZST, TypedLayout::ZST)
        }
        NodeKind::Block { label } => {
            let num_defers_at_start = ctx.defers.len();

            let (to, to_layout) = ctx.create_reg_and_typed_layout(TypeId::Node(ctx.variant_id, node.id));

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

            let (from, _) = emit_node(ctx, children.next().unwrap());
            ctx.flush_value_to(to, &from, to_layout);

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

            (Value::Stack(to), to_layout)
        }
        NodeKind::ResolvedGlobal(id, _) => {
            let (ptr, _) = ctx.program.get_member_value(*id);

            let to_layout = ctx.get_typed_layout(node_type_id);

            if let type_infer::TypeKind::Function = ctx.types.get(TypeId::Node(ctx.variant_id, node.id)).kind() {
                let function_id = unsafe { *(ptr.as_ptr() as *const FunctionId) };
                if !ctx.calling.contains(&function_id) {
                    ctx.calling.push(function_id);
                }
            }

            (Value::Constant { constant: ptr, offset: 0 }, to_layout)
        }
        NodeKind::ExpressiveFunctionCall => {
            let mut children = node.children.into_iter();
            let first_arg = children.next().unwrap();
            let calling_node = children.next().unwrap();

            // @Copypasta from FunctionCall
            let children = std::iter::once(first_arg).chain(children);

            let (to, to_layout) = ctx.create_reg_and_typed_layout(TypeId::Node(ctx.variant_id, node.id));
            let (calling, calling_layout) = emit_node(ctx, calling_node.clone());
            let calling_type = ctx.types.get(TypeId::Node(ctx.variant_id, calling_node.id));
            // @Performance
            let output_args = calling_type.args().to_vec().into_iter().skip(1).map(|v| {
                ctx.create_reg_and_typed_layout(v)
            }).collect::<Vec<_>>();

            if let Some(AdditionalInfoKind::FunctionCall(args)) = ctx.additional_info.get(&(ctx.variant_id, node.id)) {
                for (arg, node) in args.iter().zip(children) {
                    match *arg {
                        FunctionArgUsage::ValueOfAssign { function_arg } => {
                            let [_, right] = node.children.into_array();
                            let (given, _) = emit_node(ctx, right);

                            let (to, to_layout) = output_args[function_arg];
                            ctx.flush_value_to(to, &given, to_layout);
                        }
                        FunctionArgUsage::Value { function_arg } => {
                            let (given, given_layout) = emit_node(ctx, node);

                            let (to, _) = output_args[function_arg];
                            ctx.flush_value_to(to, &given, given_layout);
                        }
                        FunctionArgUsage::TupleElement { function_arg, field } => {
                            let (given, given_layout) = emit_node(ctx, node);

                            let calling_type = ctx.types.get(TypeId::Node(ctx.variant_id, calling_node.id));
                            let arg_type_id = calling_type.args()[function_arg + 1];
                            let member = ctx.types.get_member_by_index(arg_type_id, field).unwrap();

                            let (to, _) = output_args[function_arg];
                            ctx.flush_value_to(get_member(to, member.offset), &given, given_layout);
                        }
                    }
                }
            } else {
                for (&(to, _), node) in output_args.iter().zip(children) {
                    let (given, given_layout) = emit_node(ctx, node);
                    ctx.flush_value_to(to, &given, given_layout);
                }
            }

            match calling {
                Value::Constant { constant, offset } => {
                    let function_id = unsafe { *constant.as_ptr().add(offset).cast::<FunctionId>() };
                    ctx.emit_call_imm((to, to_layout), function_id, output_args, calling_node.loc);
                }
                _ => {
                    let calling = ctx.flush_value(&calling, calling_layout);
                    ctx.emit_call((to, to_layout), calling, output_args, calling_node.loc);
                }
            }

            (Value::Stack(to), to_layout)
        }
        NodeKind::FunctionCall => {
            let mut children = node.children.into_iter();
            let calling_node = children.next().unwrap();

            let (to, to_layout) = ctx.create_reg_and_typed_layout(TypeId::Node(ctx.variant_id, node.id));
            let (calling, calling_layout) = emit_node(ctx, calling_node.clone());
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
                            let (given, _) = emit_node(ctx, right);

                            let (to, to_layout) = output_args[function_arg];
                            ctx.flush_value_to(to, &given, to_layout);
                        }
                        FunctionArgUsage::Value { function_arg } => {
                            let (given, given_layout) = emit_node(ctx, node);

                            let (to, _) = output_args[function_arg];
                            ctx.flush_value_to(to, &given, given_layout);
                        }
                        FunctionArgUsage::TupleElement { function_arg, field } => {
                            let (given, given_layout) = emit_node(ctx, node);

                            let calling_type = ctx.types.get(TypeId::Node(ctx.variant_id, calling_node.id));
                            let arg_type_id = calling_type.args()[function_arg + 1];
                            let member = ctx.types.get_member_by_index(arg_type_id, field).unwrap();

                            let (to, _) = output_args[function_arg];
                            ctx.flush_value_to(get_member(to, member.offset), &given, given_layout);
                        }
                    }
                }
            } else {
                for (&(to, _), node) in output_args.iter().zip(children) {
                    let (given, given_layout) = emit_node(ctx, node);
                    ctx.flush_value_to(to, &given, given_layout);
                }
            }

            match calling {
                Value::Constant { constant, offset } => {
                    let function_id = unsafe { *constant.as_ptr().add(offset).cast::<FunctionId>() };
                    ctx.emit_call_imm((to, to_layout), function_id, output_args, calling_node.loc);
                }
                _ => {
                    let calling = ctx.flush_value(&calling, calling_layout);
                    ctx.emit_call((to, to_layout), calling, output_args, calling_node.loc);
                }
            }

            (Value::Stack(to), to_layout)
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
            let to_layout = ctx.get_typed_layout(node_type_id);

            (Value::Immediate(size.to_le_bytes()), to_layout)
        }
        NodeKind::TypeAsValue => {
            let [inner] = node.children.as_array();
            let inner_type = TypeId::Node(ctx.variant_id, inner.id);
            let compiler_type = ctx.types.value_to_compiler_type(inner_type);

            let imm = Value::Immediate((compiler_type.0 as *const _ as usize as u64).to_le_bytes());
            let layout = ctx.get_typed_layout(node_type_id);
            (imm, layout)
        }
        NodeKind::PolymorphicArgument(_) | NodeKind::AnonymousMember { .. } => {
            let &AdditionalInfoKind::Constant(constant) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };
            let inner_type = TypeId::Node(ctx.variant_id, node.id);
            let layout = ctx.get_typed_layout(inner_type);

            (Value::Constant { constant, offset: 0 }, layout)
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

            let layout = ctx.get_typed_layout(node_type_id);
            (Value::Constant { constant: ptr, offset: 0 }, layout)
        }
        NodeKind::BuiltinFunction(_) | NodeKind::FunctionDeclaration { .. } => {
            if ctx.emit_inner_function_declarations {
                let &AdditionalInfoKind::Function(id) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };

                let inner_type = TypeId::Node(ctx.variant_id, node.id);
                let compiler_type = ctx.types.value_to_compiler_type(inner_type);
                let constant_ref = ctx.program.insert_buffer(compiler_type, &id as *const _ as *const u8);

                // Emit the function itself
                emit_function_declaration(
                    ctx.thread_context,
                    ctx.program,
                    ctx.locals,
                    ctx.types,
                    node,
                    ctx.additional_info,
                    node.id,
                    ctx.variant_id,
                    node.loc,
                    id,
                    true,
                );


                let layout = ctx.get_typed_layout(node_type_id);
                (Value::Constant { constant: constant_ref, offset: 0 }, layout)
            } else {
                let &AdditionalInfoKind::Function(id) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };

                let inner_type = TypeId::Node(ctx.variant_id, node.id);
                let compiler_type = ctx.types.value_to_compiler_type(inner_type);
                let constant_ref = ctx.program.insert_buffer(compiler_type, &id as *const _ as *const u8);

                let layout = ctx.get_typed_layout(node_type_id);
                (Value::Constant { constant: constant_ref, offset: 0 }, layout)
            }
        }
        NodeKind::Is => {
            let &AdditionalInfoKind::IsExpression(comparison_id) = &ctx.additional_info[&(ctx.variant_id, node.id)] else { panic!() };
            let layout = ctx.get_typed_layout(node_type_id);

            let value = ctx.types.get_comparison_result(comparison_id);
            (Value::Immediate((value as u64).to_le_bytes()), layout)
        }
        c => unreachable!("This node should not reach emission: {:?}", c),
    }
}

fn emit_declarative_lvalue<'a>(
    ctx: &mut Context<'a, '_>,
    mut node: NodeView<'a>,
    from: &Value,
    is_declaring: bool,
) {
    ctx.emit_debug(node.loc);
    let node_type_id = TypeId::Node(ctx.variant_id, node.id);

    match &node.kind {
        NodeKind::Member { .. } => {
            debug_assert!(!is_declaring);

            let to = emit_lvalue(ctx, false, node);
            let layout = ctx.get_typed_layout(node_type_id);
            ctx.flush_value_to_lvalue(&to, from, layout);
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
            match *from {
                Value::Tuple(ref values) => {
                    for (child, (value, _)) in node.children.into_iter().zip(values) {
                        emit_declarative_lvalue(ctx, child, value, is_declaring);
                    }
                }
                _ => {
                    // TODO: We want to be able to get fields off of value, which can be done somewhat efficiently with
                    // stack values, references(probably), e.t.c.
                    let node_layout = ctx.get_typed_layout(node_type_id);
                    let from = ctx.flush_value(&from, node_layout);

                    let mut temp = Vec::with_capacity(node.children.len());
                    let mut child_layouting = StructLayout::new(0);
                    for child in node.children.into_iter() {
                        let (to, child_layout) = ctx.create_reg_and_typed_layout(TypeId::Node(ctx.variant_id, child.id));
                        let offset = child_layouting.next(child_layout.layout);
                        ctx.emit_move(to, get_member(from, offset), child_layout.layout);
                        temp.push(to);
                    }

                    for (child, to) in node.children.into_iter().zip(temp) {
                        emit_declarative_lvalue(ctx, child, &Value::Stack(to), is_declaring);
                    }
                }
            }
        }
        NodeKind::ArrayLiteral => {
            let node_layout = ctx.get_typed_layout(node_type_id);
            let from = ctx.flush_value(&from, node_layout);

            let mut temp = Vec::with_capacity(node.children.len());
            let mut offset = 0;
            for child in node.children.into_iter() {
                let (to, child_layout) = ctx.create_reg_and_layout(TypeId::Node(ctx.variant_id, child.id));
                ctx.emit_move(to, get_member(from, offset), child_layout);
                offset += child_layout.size;
                temp.push(to);
            }

            for (child, to) in node.children.into_iter().zip(temp) {
                emit_declarative_lvalue(ctx, child, &Value::Stack(to), is_declaring);
            }
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            let node_layout = ctx.get_typed_layout(node_type_id);
            let from = ctx.flush_value(&from, node_layout);

            debug_assert!(!is_declaring);
            let [operand] = node.children.as_array();
            let (pointer, pointer_layout) = emit_node(ctx, operand);
            let pointer = ctx.flush_value(&pointer, pointer_layout);
            let layout = *ctx.types.get(node_type_id).layout.unwrap();
            ctx.emit_indirect_move(pointer, from, layout);
        }
        NodeKind::Local { local_id, .. } => {
            let node_layout = ctx.get_typed_layout(node_type_id);

            if is_declaring {
                let local = ctx.locals.get(*local_id);
                let type_id = TypeId::Node(ctx.variant_id, local.declared_at.unwrap());
                let (local_value, _) = ctx.create_reg_and_layout(type_id);
                let local = ctx.locals.get_mut(*local_id);
                local.value = Some(local_value);
                ctx.flush_value_to(local_value, from, node_layout);
            } else {
                let to = ctx.locals.get(*local_id).value.unwrap();
                ctx.flush_value_to(to, from, node_layout);
            }
        }
        NodeKind::Parenthesis | NodeKind::Pack | NodeKind::Unpack => {
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
    // We don't return a typed layout, because we know it's going to be a pointer.
) -> LValue {
    ctx.emit_debug(node.loc);

    let node_type_id = TypeId::Node(ctx.variant_id, node.id);
    // @TODO: Creating all these types suck, maybe we should remove the damn `Global` thing from registers,
    // and instead let them just be pointers to values? These pointers wouldn't even be considered pointers from
    // the language, but just registers that need to point to things.
    let ref_type_id = ctx.types.add_type(type_infer::TypeKind::Reference, Args([(node_type_id, Reason::temp_zero())]), ());

    match &node.kind {
        NodeKind::Member { name } => {
            let [of] = node.children.as_array();

            let mut of_type_id = TypeId::Node(ctx.variant_id, of.id);
            let mut parent_value = emit_lvalue(ctx, can_reference_temporaries, of.clone());

            loop {
                match ctx.types.get(of_type_id).kind.as_ref().unwrap() {
                    type_infer::Type { kind: type_infer::TypeKind::Reference, args } => {
                        let new_of = args.as_ref().unwrap()[0];
                        match parent_value {
                            LValue::Specific(pointer) => {
                                parent_value = LValue::Pointer { pointer, offset: 0 };
                            }
                            LValue::Pointer { .. } => {
                                let value = ctx.lvalue_as_value(&parent_value);
                                let pointer = ctx.flush_value(&value, TypedLayout::PTR);
                                parent_value = LValue::Pointer { pointer, offset: 0 };
                            }
                        }
                        of_type_id = new_of;
                    }
                    type_infer::Type { kind: type_infer::TypeKind::Unique(_) | type_infer::TypeKind::Enum { .. }, args } => {
                        of_type_id = args.as_ref().unwrap()[0];
                    }
                    _ => break,
                }
            }

            let member = ctx.types.get_member_by_name(of_type_id, *name).unwrap();

            ctx.get_member_of_lvalue(&parent_value, member.offset)
        }
        NodeKind::Pack | NodeKind::Unpack => {
            let [operand] = node.children.as_array();
            emit_lvalue(ctx, can_reference_temporaries, operand)
        }
        NodeKind::Unary {
            op: UnaryOp::Dereference,
        } => {
            let [operand] = node.children.as_array();
            let (value, _) = emit_node(ctx, operand);
            ctx.value_as_lvalue(&value)
        }
        NodeKind::Local { local_id, .. } => {
            let from = ctx.locals.get(*local_id).value.unwrap();
            LValue::Specific(from)
        }
        NodeKind::ResolvedGlobal(id, _) => {
            let to = ctx.create_reg(ref_type_id);
            let (from_ref, from_type) = ctx.program.get_member_value(*id);
            ctx.emit_ref_to_global(to, from_ref, from_type);
            LValue::Pointer { pointer: to, offset: 0 }
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
                let (from, from_layout) = emit_node(ctx, node);
                let flushed = ctx.flush_value(&from, from_layout);
                LValue::Specific(flushed)
            } else {
                unreachable!(
                    "{:?} is not an lvalue. This is just something I haven't implemented checking for in the compiler yet",
                    kind
                )
            }
        }
    }
}

#[derive(Debug, Clone)]
enum LValue {
    // The lvalue is referencing a specific stack value
    Specific(StackValue),
    // A pointer on the stack
    Pointer {
        pointer: StackValue,
        // The offset to the value behind the pointer.
        offset: usize,
    },
}

#[derive(Debug, Clone)]
enum Value {
    Immediate([u8; 8]),
    Zeroed,
    Uninit,
    Constant {
        constant: ConstantRef,
        offset: usize,
    },
    Stack(StackValue),
    // A pointer to a stack value, but the pointer is only imaginary.
    // Once flushes the pointer would get pushed to the stack, though.
    PointerToStack(StackValue),
    // A pointer in the stack, that is pointing to the value we want (though the value
    // we actually want is also offset by an offset).
    PointerInStack {
        stack_value: StackValue,
        offset: usize,
    },
    Tuple(Vec<(Value, TypedLayout)>),
}

impl Value {
    const ZST: Value = Value::Stack(StackValue::ZST);
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
    pub emit_inner_function_declarations: bool,

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

            self.last_location = Some(loc);
            self.instr.push(Instr::DebugLocation(loc));
        }
    }

    // Converts a value (has to be a pointer),
    // into an lvalue
    fn value_as_lvalue(&mut self, value: &Value) -> LValue {
        match *value {
            Value::PointerToStack(stack_value) => {
                LValue::Specific(stack_value)
            }
            Value::Stack(pointer) => {
                LValue::Pointer {
                    pointer,
                    offset: 0,
                }
            }
            _ => {
                let pointer = self.flush_value(value, TypedLayout::PTR);
                LValue::Pointer {
                    pointer,
                    offset: 0,
                }
            }
        }
    }

    // Converts an lvalue into a value.
    fn lvalue_as_value(&mut self, lvalue: &LValue) -> Value {
        match *lvalue {
            LValue::Specific(stack_value) => Value::PointerToStack(stack_value),
            LValue::Pointer { pointer, offset } => {
                // TODO: I want to have some way to speficy that you have an at most
                // 64 bit stack primitive, with an immediate addition to it, which
                // could encode this kind of thing.
                if offset == 0 {
                    Value::Stack(pointer)
                } else {
                    let temp = self.create_reg_with_layout(Layout::PTR);
                    self.emit_move(temp, pointer, Layout::PTR);
                    self.emit_binary_imm_u64(BinaryOp::Add, temp, temp, offset as u64);
                    Value::Stack(temp)
                }
            }
        }
    }

    fn get_member_of_lvalue(&mut self, value: &LValue, member_offset: usize) -> LValue {
        match *value {
            LValue::Specific(stack_value) => LValue::Specific(StackValue(stack_value.0 + member_offset)),
            LValue::Pointer { pointer, offset } => LValue::Pointer { pointer, offset: offset + member_offset },
        }
    }

    fn get_member_of_value(&mut self, value: &Value, value_layout: TypedLayout, member_number: usize, member_offset: usize) -> Value {
        match *value {
            Value::Zeroed => Value::Zeroed,
            Value::Constant { constant, offset } => {
                Value::Constant { constant, offset: offset + member_offset }
            }
            Value::Stack(value) => {
                Value::Stack(StackValue(value.0 + member_offset))
            }
            Value::PointerToStack(_) => unreachable!("Pointers don't have members"),
            Value::Tuple(ref fields) => {
                // We assume the tuple is the correct size, which we can do because of type
                // checking (or at least, should be able to do.
                // @Speed: This is slow because of the clone, I don't know if we can fix this.
                // Ultimately, I'd like to get rid of allocations in Value to begin with.
                fields[member_number].0.clone()
            }
            Value::PointerInStack { stack_value, offset } => {
                Value::PointerInStack { stack_value, offset: offset + member_offset }
            }
            _ => {
                // Worst case scenario is we just have to flush the value and get the member that way.
                let stack_value = self.flush_value(value, value_layout);
                Value::Stack(StackValue(stack_value.0 + member_offset))
            }
        }
    }

    // TODO: Do we want to do something different from flush_value_to here, because we can in theory just return the original stack value
    // for stack values. Depends on if it should be mutated or not.
    fn flush_value(&mut self, from: &Value, layout: TypedLayout) -> StackValue {
        let temp = self.create_reg_with_layout(layout.layout);
        self.flush_value_to(temp, from, layout);
        temp
    }

    fn flush_value_to_lvalue(&mut self, to: &LValue, from: &Value, layout: TypedLayout) {
        if layout.size == 0 { return; }

        match (to, from) {
            (&LValue::Specific(to_stack), &Value::Immediate(num)) => {
                self.emit_move_imm(to_stack, num, layout.layout);
            }
            (&LValue::Pointer { pointer, offset }, &Value::Immediate(num)) => {
                let temp = self.create_reg_with_layout(layout.layout);
                self.emit_move_imm(temp, num, layout.layout);
                self.emit_indirect_move_with_offset(pointer, offset, temp, layout.layout);
            }
            (_, &Value::Constant { constant, offset }) => {
                let to_value = self.lvalue_as_value(to);
                let to_ptr = self.flush_value(&to_value, TypedLayout::PTR);

                let temp_ptr = self.create_reg_with_layout(Layout::PTR);
                let temp_value = self.create_reg_with_layout(layout.layout);
                self.instr.push(Instr::RefGlobal { to_ptr: temp_ptr, global: constant });
                self.emit_dereference(temp_value, temp_ptr, layout.layout);
                self.emit_indirect_move_with_offset(to_ptr, offset, temp_value, layout.layout);
            }
            (_, &Value::Stack(value)) => {
                let to_value = self.lvalue_as_value(to);
                let to_ptr = self.flush_value(&to_value, TypedLayout::PTR);
                self.emit_indirect_move(to_ptr, value, layout.layout);
            }
            (_, &Value::Zeroed) => {
                let to_value = self.lvalue_as_value(to);
                let to_ptr = self.flush_value(&to_value, TypedLayout::PTR);
                let temp = self.create_reg_with_layout(layout.layout);
                self.emit_set_to_zero(temp, layout.layout);
                self.emit_indirect_move(to_ptr, temp, layout.layout);
            }
            (_, &Value::Uninit) => {}
            (_, &Value::PointerToStack(stack_value)) => {
                let to_value = self.lvalue_as_value(to);
                let to_ptr = self.flush_value(&to_value, TypedLayout::PTR);
                let temp = self.create_reg_with_layout(Layout::PTR);
                self.emit_reference(temp, stack_value);
                self.emit_indirect_move(to_ptr, temp, layout.layout);
            }
            (_, &Value::PointerInStack { stack_value, offset }) => {
                let to_value = self.lvalue_as_value(to);
                let to_ptr = self.flush_value(&to_value, TypedLayout::PTR);

                let from = self.create_reg_with_layout(layout.layout);
                self.emit_dereference_with_offset(from, stack_value, offset, layout.layout);
                self.emit_indirect_move(to_ptr, from, layout.layout);
            }
            (_, &Value::Tuple(ref fields)) => {
                // TODO: Later, we want a "flush value offset", that lets you flush to an offset of something.
                let temp = self.create_reg_with_layout(Layout::PTR);
                let to_value = self.lvalue_as_value(to);
                self.flush_value_to(temp, &to_value, TypedLayout::PTR);
                let mut tuple_layout = StructLayout::new(0);
                let mut prev_offset = 0;
                for &(ref field, field_layout) in fields {
                    let new_offset = tuple_layout.next(field_layout.layout);
                    self.emit_binary_imm_u64(BinaryOp::Add, temp, temp, (new_offset - prev_offset) as u64);
                    prev_offset = new_offset;
                    self.flush_value_to_indirect(temp, field, field_layout);
                }
            }
        }
    }

    fn flush_value_to_indirect(&mut self, to_ptr: StackValue, from: &Value, layout: TypedLayout) {
        self.flush_value_to_lvalue(&LValue::Specific(to_ptr), from, layout);
    }

    fn flush_value_to(&mut self, to: StackValue, from: &Value, layout: TypedLayout) {
        if layout.size == 0 { return; }

        match *from {
            Value::Immediate(num) => {
                self.emit_move_imm(to, num, layout.layout);
            }
            Value::Constant { constant, offset } => {
                // TODO: This can be done more efficiently if RefGlobal allows an offset.
                let temp = self.create_reg_with_layout(Layout::PTR);
                self.instr.push(Instr::RefGlobal { to_ptr: temp, global: constant });
                self.emit_binary_imm_u64(BinaryOp::Add, temp, temp, offset as u64);
                self.emit_dereference(to, temp, layout.layout);
            }
            Value::Stack(value) => {
                self.emit_move(to, value, layout.layout);
            }
            Value::Zeroed => {
                self.emit_set_to_zero(to, layout.layout);
            }
            Value::Uninit => {}
            Value::PointerToStack(stack_value) => {
                self.emit_reference(to, stack_value);
            }
            Value::PointerInStack { stack_value, offset } => {
                if offset == 0 {
                    self.emit_dereference(to, stack_value, layout.layout);
                } else {
                    // TODO: This can be done more efficiently if Dereference allows an offset.
                    let temp = self.create_reg_with_layout(Layout::PTR);
                    self.emit_move(temp, stack_value, Layout::PTR);
                    self.emit_binary_imm_u64(BinaryOp::Add, temp, temp, offset as u64);
                    self.emit_dereference(to, temp, layout.layout);
                }
            }
            Value::Tuple(ref fields) => {
                let mut tuple_layout = StructLayout::new(0);
                for &(ref field, field_layout) in fields {
                    let new_offset = tuple_layout.next(field_layout.layout);
                    self.flush_value_to(StackValue(to.0 + new_offset), field, field_layout);
                }
            }
        }
    }

    fn get_typed_layout(&mut self, type_id: TypeId) -> TypedLayout {
        let number_type = self.to_number_type(type_id);
        let type_ = self.types.get(type_id);
        let layout = *type_.layout.unwrap();
        TypedLayout {
            primitive: number_type,
            layout,
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
            self.instr.push(Instr::Dereference { to, from_ptr: temp, offset: 0, size: layout.size });
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

    fn emit_dereference_with_offset(&mut self, to: StackValue, from_ptr: StackValue, offset: usize, layout: Layout) {
        if layout.size != 0 {
            self.instr.push(Instr::Dereference { to, from_ptr, offset, size: layout.size });
        }
    }

    fn emit_dereference(&mut self, to: StackValue, from_ptr: StackValue, layout: Layout) {
        if layout.size != 0 {
            self.instr.push(Instr::Dereference { to, from_ptr, offset: 0, size: layout.size });
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

    fn emit_indirect_move_with_offset(&mut self, to_ptr: StackValue, offset: usize, from: StackValue, layout: Layout) {
        if layout.size != 0 {
            self.instr.push(Instr::IndirectMove {
                to_ptr,
                from,
                offset,
                size: layout.size,
            });
        }
    }

    fn emit_indirect_move(&mut self, to_ptr: StackValue, from: StackValue, layout: Layout) {
        if layout.size != 0 {
            self.instr.push(Instr::IndirectMove {
                to_ptr,
                from,
                offset: 0,
                size: layout.size,
            });
        }
    }

    fn emit_call_imm(&mut self, to: (StackValue, TypedLayout), function_id: FunctionId, args: Vec<(StackValue, TypedLayout)>, loc: Location) {
        self.instr.push(Instr::CallImm { to, function_id, args, loc });
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
            type_infer::TypeKind::Unique(_) | type_infer::TypeKind::Enum { .. } => {
                let arg = type_.args()[0];
                self.to_number_type(arg)
            }
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
