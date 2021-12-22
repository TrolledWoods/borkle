use crate::ir::{Instr, Routine, Value};
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::{BuiltinFunction, FunctionId, Program};
use crate::types::{IntTypeKind, PointerInType, Type, TypeKind, TYPES};
use std::fmt;
use std::fmt::Write;

pub fn function_declaration(
    output: &mut String,
    name: impl fmt::Display,
    args: &[Type],
    returns: Type,
) {
    write!(output, "{} {}(", c_format_type_or_void(returns), name).unwrap();
    let mut has_emitted = false;
    for (i, arg) in args.iter().enumerate() {
        if arg.size() == 0 {
            continue;
        }

        if has_emitted {
            output.push_str(", ");
        }

        write!(output, "{} reg_{}", c_format_type(*arg), i).unwrap();
        has_emitted = true;
    }
    output.push(')');
}

pub fn function_pointer_type(
    output: &mut String,
    name: impl fmt::Display,
    args: &[Type],
    returns: Type,
) {
    write!(output, "{} (*{})(", c_format_type_or_void(returns), name).unwrap();
    let mut has_emitted = false;
    for arg in args {
        if arg.size() == 0 {
            continue;
        }

        if has_emitted {
            output.push_str(", ");
        }

        write!(output, "{}", c_format_type(*arg)).unwrap();
        has_emitted = true;
    }
    output.push(')');
}

pub fn entry_point(output: &mut String, entry: FunctionId) {
    output.push_str("int main() {\n");
    write!(output, "    return {}();\n", c_format_function(entry)).unwrap();
    output.push_str("}\n");
}

fn c_format_value(value: &Value) -> impl fmt::Display + '_ {
    Formatter(move |f| match value {
        Value::Register(id, _) => write!(f, "reg_{}", id),
        Value::Global(ptr, type_) => {
            if let TypeKind::Function { .. } = type_.kind() {
                write!(
                    f,
                    "{}",
                    c_format_function(unsafe { *ptr.as_ptr().cast::<FunctionId>() })
                )?;
            } else {
                debug_assert!(type_.size() != 0);

                // FIXME: Check if this can just be a normal cast and not this kind of pointer
                // cast.
                write!(
                    f,
                    "(*({}*)&global_{})",
                    c_format_type(*type_),
                    ptr.as_ptr() as usize
                )?;
            }

            Ok(())
        }
    })
}

pub fn declare_constants(output: &mut String, program: &mut Program) {
    let constant_data = program.constant_data();
    for constant in constant_data
        .iter()
        .filter(|constant| !constant.type_.pointers().is_empty())
    {
        let ptr = constant.ptr.as_ptr();
        write!(
            output,
            "const struct {} {{ ",
            c_format_global_temp_type(ptr as usize),
        )
        .unwrap();

        let mut pointers = constant.type_.pointers().iter().peekable();
        for i in (0..constant.type_.size()).step_by(8) {
            match pointers.peek() {
                Some(&(offset, ptr_type)) if *offset == i => {
                    match ptr_type {
                        PointerInType::Function { args, returns, .. } => {
                            function_pointer_type(
                                output,
                                c_format_struct_member(i),
                                args,
                                *returns,
                            );
                            output.push_str("; ");
                        }
                        _ => {
                            write!(output, "void *{}; ", c_format_struct_member(i)).unwrap();
                        }
                    }
                    pointers.next();
                }
                Some(_) | None => {
                    write!(output, "uint64_t {}; ", c_format_struct_member(i)).unwrap();
                }
            }
        }

        write!(output, "}} {};\n", c_format_global(ptr as usize),).unwrap();
    }
}

pub fn instantiate_constants(output: &mut String, program: &mut Program) {
    for constant in program.constant_data() {
        let ptr = constant.ptr.as_ptr();
        if constant.type_.pointers().is_empty() {
            write!(
                output,
                "const uint64_t {}[{}] = {{",
                c_format_global(ptr as usize),
                (constant.type_.size() + 7) / 8,
            )
            .unwrap();
        } else {
            write!(
                output,
                "const struct {} {} = {{",
                c_format_global_temp_type(ptr as usize),
                c_format_global(ptr as usize),
            )
            .unwrap();
        }

        let mut pointers = constant.type_.pointers().iter().peekable();
        for i in (0..constant.type_.size()).step_by(8) {
            match pointers.peek() {
                Some(&(offset, pointer_kind)) if *offset == i => {
                    let ptr_num = unsafe { *ptr.add(i).cast::<usize>() };
                    if ptr_num == 0 {
                        output.push_str("NULL");
                    } else if let PointerInType::Function { .. } = pointer_kind {
                        write!(output, "&{}", c_format_function(ptr_num.into())).unwrap();
                    } else {
                        write!(output, "&{}", c_format_global(ptr_num)).unwrap();
                    }
                    pointers.next();
                }
                _ => {
                    write!(output, "{}", unsafe { *ptr.add(i).cast::<u64>() }).unwrap();
                }
            }

            output.push_str(", ");
        }
        write!(output, "}}; // {}\n", constant.type_).unwrap();
    }
}

pub fn routine_to_c(output: &mut String, routine: &Routine, arg_types: &[Type], return_type: Type) {
    match routine {
        &Routine::Builtin(kind) => {
            output.push_str("    // Builtin function!\n");

            let values: Vec<_> = arg_types
                .iter()
                .copied()
                .enumerate()
                .map(|(i, type_)| Value::Register(i, type_))
                .collect();

            let returns = Value::Register(arg_types.len(), return_type);
            if return_type.size() != 0 {
                write!(
                    output,
                    "    {} {};",
                    c_format_type(return_type),
                    c_format_value(&returns)
                )
                .unwrap();
            }

            builtin_function(output, kind, &values, returns);

            if return_type.size() != 0 {
                write!(output, "    return {};\n", c_format_value(&returns)).unwrap();
            }
        }
        Routine::UserDefined(routine) => {
            // write!(output, "    // Declare registers\n").unwrap();
            for (i, register) in routine
                .registers
                .locals
                .iter()
                .enumerate()
                .skip(arg_types.len())
            {
                if register.type_.size() != 0 {
                    write!(
                        output,
                        "    {} reg_{}; // {}\n",
                        c_format_type(register.type_),
                        i,
                        register.type_
                    )
                    .unwrap();
                }
            }

            // write!(output, "    // Code\n").unwrap();
            for instr in &routine.instr {
                // write!(output, "    // {:?}\n", instr).unwrap();
                output.push_str("    ");
                match instr {
                    Instr::TruncateInt { to, from, .. } | Instr::ExtendInt { to, from, .. } => {
                        let Value::Register(_, to_type) = to else {
                            unreachable!("Assigned to global in ir, should probably make this impossible in the type system in the future")
                        };
                        write!(
                            output, "{} = ({}){};\n",
                            c_format_value(to),
                            c_format_type(*to_type),
                            c_format_value(from),
                        ).unwrap();
                    }
                    Instr::SetToZero { to, size } => {
                        write!(output, "memset(&{}, 0, {});\n", c_format_value(to), size,).unwrap();
                    }
                    Instr::Call { to, pointer, args, loc: _ } => {
                        if to.size() != 0 {
                            write!(
                                output,
                                "{} = {}(",
                                c_format_value(to),
                                c_format_value(pointer),
                            )
                            .unwrap();
                        } else {
                            write!(output, "{}(", c_format_value(pointer),).unwrap();
                        }
                        let mut has_emitted = false;
                        for arg in args {
                            if arg.size() == 0 {
                                continue;
                            }

                            if has_emitted {
                                output.push_str(", ");
                            }
                            write!(output, "{}", c_format_value(arg)).unwrap();
                            has_emitted = true;
                        }
                        output.push_str(");\n");
                    }
                    Instr::Increment { value } => {
                        write!(output, "{0} = {0} + 1;\n", c_format_value(value)).unwrap();
                    }
                    Instr::Binary {
                        op: BinaryOp::Range,
                        to,
                        a,
                        b,
                    } => {
                        write!(
                            output,
                            "{}.start = {};\n",
                            c_format_value(to),
                            c_format_value(a),
                        )
                        .unwrap();
                        write!(
                            output,
                            "{}.end = {};\n",
                            c_format_value(to),
                            c_format_value(b),
                        )
                        .unwrap();
                    }
                    Instr::Binary { op, to, a, b } => {
                        let op_name = match op {
                            BinaryOp::And => "&&",
                            BinaryOp::Or => "||",
                            BinaryOp::Equals => "==",
                            BinaryOp::NotEquals => "!=",
                            BinaryOp::LargerThanEquals => ">=",
                            BinaryOp::LargerThan => ">",
                            BinaryOp::LessThanEquals => "<=",
                            BinaryOp::LessThan => "<",
                            BinaryOp::Add => "+",
                            BinaryOp::ShiftLeft => "<<",
                            BinaryOp::ShiftRight => ">>",
                            BinaryOp::Sub => "-",
                            BinaryOp::Mult => "*",
                            BinaryOp::Modulo => "%",
                            BinaryOp::Div => "/",
                            BinaryOp::BitAnd => "&",
                            BinaryOp::BitOr => "|",
                            _ => unreachable!("Cannot output this operator to C, it's supposed to be replaced by the compiler in an earlier stage"),
                        };

                        write!(
                            output,
                            "{} = {} {} {};\n",
                            c_format_value(to),
                            c_format_value(a),
                            op_name,
                            c_format_value(b)
                        )
                        .unwrap();
                    }
                    Instr::Unary { op, to, from } => {
                        let op_name = match op {
                            UnaryOp::Negate => "-",
                            UnaryOp::Not => "!",
                            UnaryOp::Dereference | UnaryOp::Reference => {
                                unreachable!()
                            }
                        };

                        write!(
                            output,
                            "{} = {}{};",
                            c_format_value(to),
                            op_name,
                            c_format_value(from)
                        )
                        .unwrap();
                    }
                    Instr::Member { to, of, member } => {
                        write!(output, "{} = {}", c_format_value(to), c_format_value(of)).unwrap();

                        of.type_().fmt_members(output, *member);

                        write!(output, ";\n").unwrap();
                    }
                    Instr::PointerToMemberOfPointer { to, of, member } => {
                        write!(
                            output,
                            "{} = &(*{})",
                            c_format_value(to),
                            c_format_value(of)
                        )
                        .unwrap();

                        of.type_().fmt_members(output, *member);

                        output.push_str(";\n");
                    }
                    Instr::Dereference { to, from } => {
                        write!(
                            output,
                            "{} = *{};\n",
                            c_format_value(to),
                            c_format_value(from)
                        )
                        .unwrap();
                    }
                    Instr::PointerToMemberOfValue { to, from, offset } => {
                        write!(output, "{} = &{}", c_format_value(to), c_format_value(from))
                            .unwrap();

                        from.type_().fmt_members(output, *offset);

                        output.push_str(";\n");
                    }
                    Instr::MoveToMemberOfValue {
                        to,
                        from,
                        size: _,
                        member,
                    } => {
                        write!(output, "{}", c_format_value(to)).unwrap();

                        to.type_().fmt_members(output, *member);

                        write!(output, " = {};\n", c_format_value(from)).unwrap();
                    }
                    Instr::MoveToMemberOfPointer {
                        to,
                        from,
                        size: _,
                        member,
                    } => {
                        write!(output, "(*{})", c_format_value(to)).unwrap();

                        to.type_()
                            .pointing_to()
                            .unwrap()
                            .fmt_members(output, *member);

                        write!(output, " = {};\n", c_format_value(from)).unwrap();
                    }
                    Instr::JumpIfZero { condition, to } => {
                        write!(
                            output,
                            "if ({} == 0) goto label_{};\n",
                            c_format_value(condition),
                            to.0
                        )
                        .unwrap();
                    }
                    Instr::Jump { to } => {
                        write!(output, "goto label_{};\n", to.0).unwrap();
                    }
                    Instr::LabelDefinition(id) => {
                        write!(output, "label_{}:;\n", id.0).unwrap();
                    }
                }
            }

            if routine.result.size() != 0 {
                write!(output, "    return {};\n", c_format_value(&routine.result)).unwrap();
            }
        }
    }
}

fn builtin_function(output: &mut String, builtin: BuiltinFunction, args: &[Value], to: Value) {
    output.push_str("    ");

    match builtin {
        BuiltinFunction::Assert => {
            write!(
                output,
                "assert({});\n",
                c_format_value(&args[0]),
            )
            .unwrap();
        }
        BuiltinFunction::StdoutWrite => {
            write!(
                output,
                "{} = fwrite({}.ptr, 1, {}.len, stdout);\n",
                c_format_value(&to),
                c_format_value(&args[0]),
                c_format_value(&args[0]),
            )
            .unwrap();
        }
        BuiltinFunction::StdoutFlush => {
            output.push_str("fflush(stdout);\n");
        }
        BuiltinFunction::StdinGetLine => {
            write!(
                output,
                "{{
                        char temp_data[512];
                        gets(temp_data);\n
                        {0}.len = strlen(temp_data);
                        {0}.ptr = malloc({0}.len);
                        memcpy({0}.ptr, temp_data, {0}.len);
                    }}\n",
                c_format_value(&to),
            )
            .unwrap();
        }
        BuiltinFunction::Alloc => {
            write!(
                output,
                "{} = malloc({});\n",
                c_format_value(&to),
                c_format_value(&args[0]),
            )
            .unwrap();
        }
        BuiltinFunction::Dealloc => {
            write!(output, "free({}.ptr);\n", c_format_value(&args[0])).unwrap();
        }
        BuiltinFunction::MemCopy => {
            write!(
                output,
                "memmove({}, {}, {});\n",
                c_format_value(&args[1]),
                c_format_value(&args[0]),
                c_format_value(&args[2])
            )
            .unwrap();
        }
        BuiltinFunction::MemCopyNonOverlapping => {
            write!(
                output,
                "memcpy({}, {}, {});\n",
                c_format_value(&args[1]),
                c_format_value(&args[0]),
                c_format_value(&args[2])
            )
            .unwrap();
        }
    }
}

pub fn append_c_type_headers(output: &mut String) {
    for &type_ in &*TYPES.lock() {
        if type_.size == 0 {
            continue;
        }

        output.push_str("typedef ");

        let mut name_is_needed = true;
        match &type_.kind {
            TypeKind::Type => output.push_str("uint64_t "),
            TypeKind::Never | TypeKind::Empty => unreachable!(),
            TypeKind::Range(internal) => {
                write!(
                    output,
                    "struct {{ {0} start; {0} end; }}",
                    c_format_type(*internal),
                )
                .unwrap();
            }
            TypeKind::Array(internal, len) => {
                write!(
                    output,
                    "struct {{ {} _0[{}] }} ",
                    c_format_type(*internal),
                    len
                )
                .unwrap();
            }

            TypeKind::VoidPtr => output.push_str("void *"),
            TypeKind::Bool => output.push_str("uint8_t "),
            TypeKind::Int(IntTypeKind::U8) => output.push_str("uint8_t "),
            TypeKind::Int(IntTypeKind::U16) => output.push_str("uint16_t "),
            TypeKind::Int(IntTypeKind::U32) => output.push_str("uint32_t "),
            TypeKind::Int(IntTypeKind::U64) => output.push_str("uint64_t "),
            TypeKind::Int(IntTypeKind::I8) => output.push_str("int8_t "),
            TypeKind::Int(IntTypeKind::I16) => output.push_str("int16_t "),
            TypeKind::Int(IntTypeKind::I32) => output.push_str("int32_t "),
            TypeKind::Int(IntTypeKind::I64) => output.push_str("int64_t "),
            TypeKind::Int(IntTypeKind::Usize) => output.push_str("uint64_t "),
            TypeKind::Int(IntTypeKind::Isize) => output.push_str("int64_t "),

            TypeKind::F32 => output.push_str("float "),
            TypeKind::F64 => output.push_str("double "),

            TypeKind::Reference { pointee, .. } => {
                write!(output, "{}", c_format_pointer_type(*pointee)).unwrap()
            }
            TypeKind::VoidBuffer => {
                write!(output, "struct{{\n  void *ptr;\n  uint64_t len;\n}}",).unwrap();
            }
            TypeKind::AnyPtr => {
                write!(output, "struct{{\n  void *ptr;\n  uint64_t type_;\n}}",).unwrap();
            }
            TypeKind::Buffer { pointee, .. } => {
                write!(
                    output,
                    "struct{{\n  {} ptr;\n  uint64_t len;\n}}",
                    c_format_pointer_type(*pointee),
                )
                .unwrap();
            }

            TypeKind::Function { args, returns } => {
                write!(
                    output,
                    "{} (*t_{}) ",
                    c_format_type_or_void(*returns),
                    type_ as *const _ as usize
                )
                .unwrap();

                output.push('(');
                let mut has_emitted = false;
                for arg in args {
                    if arg.size() == 0 {
                        continue;
                    }

                    if has_emitted {
                        output.push_str(", ");
                    }

                    write!(output, "{}", c_format_type(*arg)).unwrap();
                    has_emitted = true;
                }
                output.push(')');

                name_is_needed = false;
            }
            TypeKind::Struct(fields) => {
                output.push_str("struct {\n");
                for (name, _, type_) in crate::types::struct_field_offsets(fields) {
                    if type_.size() != 0 {
                        write!(output, "    {} {};\n", c_format_type(type_), name).unwrap();
                    }
                }
                output.push('}');
            }
        }

        if name_is_needed {
            write!(output, "t_{}", type_ as *const _ as usize).unwrap();
        }

        write!(output, "; // {}\n", type_.kind).unwrap();
    }
}

pub fn c_format_struct_member(member_id: usize) -> impl fmt::Display {
    Formatter(move |f| write!(f, "_{}", member_id))
}

pub fn c_format_global_temp_type(global: usize) -> impl fmt::Display {
    Formatter(move |f| write!(f, "t_global_{}", global))
}

pub fn c_format_global(global: usize) -> impl fmt::Display {
    Formatter(move |f| write!(f, "global_{}", global))
}

pub fn c_format_function(function: FunctionId) -> impl fmt::Display {
    let num: usize = function.into();
    Formatter(move |f| write!(f, "function_{}", num))
}

/// Formats a pointer type(the given type being the inner type)
pub fn c_format_pointer_type(type_: Type) -> impl fmt::Display {
    Formatter(move |f| {
        if type_.size() == 0 {
            write!(f, "void *")
        } else {
            write!(f, "t_{} *", type_.as_ptr() as usize)
        }
    })
}

/// Formats a type as C. The type can't be zero sized.
pub fn c_format_type(type_: Type) -> impl fmt::Display {
    debug_assert_ne!(type_.size(), 0);

    Formatter(move |f| write!(f, "t_{}", type_.as_ptr() as usize))
}

/// Formats a type as C. If the type is zero sized, it uses void instead
pub fn c_format_type_or_void(type_: Type) -> impl fmt::Display {
    Formatter(move |f| {
        if type_.size() == 0 {
            write!(f, "void")
        } else {
            write!(f, "t_{}", type_.as_ptr() as usize)
        }
    })
}

pub struct Formatter<F>(F)
where
    F: for<'a> Fn(&mut fmt::Formatter<'a>) -> fmt::Result;

impl<F> fmt::Display for Formatter<F>
where
    F: for<'a> Fn(&mut fmt::Formatter<'a>) -> fmt::Result,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.0)(f)
    }
}
