// I think using new line characters is cleaner i nthis case because
// there are so many friggin writes.
#![allow(clippy::write_with_newline)]

use crate::ir::{Instr, Routine, Value};
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::Program;
use crate::types::{IntTypeKind, Type, TypeKind, TYPES};
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

        write!(output, "{} arg_{}", c_format_type(*arg), i).unwrap();
        has_emitted = true;
    }
    output.push(')');
}

pub fn entry_point(output: &mut String, entry: *const u8) {
    output.push_str("void main() {\n");
    output.push_str("    init();\n");
    write!(
        output,
        "    printf(\"%d\\n\", global_{}());\n",
        entry as usize
    )
    .unwrap();
    output.push_str("}\n");
}

fn c_format_value(value: &Value) -> impl fmt::Display + '_ {
    Formatter(move |f| match value {
        Value::Register(id, _) => write!(f, "reg_{}", id),
        Value::Global(ptr, type_) => {
            if let TypeKind::Function { .. } = type_.kind() {
                write!(f, "global_{}", unsafe { *ptr.as_ptr().cast::<*const u8>() }
                    as usize)?;
            } else {
                debug_assert!(type_.size() != 0);

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

pub fn declare_constants(output: &mut String, program: &Program) {
    let constant_data = program.constant_data.lock();
    let external_symbols = program.external_symbols.lock();
    for (_, &(type_, name)) in external_symbols.iter() {
        if let TypeKind::Function { args, returns, .. } = type_.kind() {
            output.push_str("extern ");
            function_declaration(output, name, args, *returns);
            output.push_str(";\n");
        } else {
            unreachable!();
        }
    }
    for constant in constant_data.iter() {
        let ptr = constant.ptr.as_ptr();
        if constant.constant_pointers.is_empty() {
            output.push_str("const ");
        }
        write!(
            output,
            "uint64_t global_{}[{}] = {{",
            ptr as usize,
            constant.size / 8
        )
        .unwrap();

        let u64_ptr = ptr.cast::<u64>();
        for i in 0..constant.size / 8 {
            write!(output, "{}, ", unsafe { *u64_ptr.add(i) }).unwrap();
        }
        output.push_str("}; \n");
    }
}

pub fn instantiate_pointers_in_constants(output: &mut String, program: &Program) {
    output.push_str("void init(void) {\n");

    let external_symbols = program.external_symbols.lock();
    let constant_data = program.constant_data.lock();
    for constant in constant_data.iter() {
        for (offset, ptr, type_) in constant.constant_pointers.iter() {
            if let TypeKind::Function {
                is_extern: true, ..
            } = type_.kind()
            {
                write!(
                    output,
                    "    global_{}[{}] = (uint64_t){};\n",
                    constant.ptr.as_ptr() as usize,
                    offset / 8,
                    external_symbols
                        .get(&unsafe { *constant.ptr.as_ptr().cast::<*const u8>() })
                        .unwrap()
                        .1
                )
                .unwrap();
            } else {
                write!(
                    output,
                    "    global_{}[{}] = (uint64_t)&global_{};\n",
                    constant.ptr.as_ptr() as usize,
                    offset / 8,
                    ptr.as_ptr() as usize,
                )
                .unwrap();
            }
        }
    }

    output.push_str("}\n");
}

pub fn routine_to_c(output: &mut String, routine: &Routine, num_args: usize) {
    write!(output, "    // Declare registers\n").unwrap();
    for (i, register) in routine.registers.locals.iter().enumerate() {
        if register.type_.size() != 0 {
            write!(output, "    {} reg_{}", c_format_type(register.type_), i,).unwrap();

            if i < num_args {
                write!(output, " = arg_{}", i).unwrap();
            }

            write!(output, "; // {}\n", register.type_).unwrap();
        }
    }

    write!(output, "    // Code\n").unwrap();
    for instr in &routine.instr {
        write!(output, "    // {:?}\n", instr).unwrap();
        output.push_str("    ");
        match instr {
            Instr::Call { to, pointer, args }
            | Instr::CallExtern {
                to, pointer, args, ..
            } => {
                write!(
                    output,
                    "{} = {}(",
                    c_format_value(to),
                    c_format_value(pointer),
                )
                .unwrap();
                let mut has_emitted = false;
                for (i, arg) in args.iter().enumerate() {
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
            Instr::Constant { to, from } => {
                let type_ = to.type_();

                write!(
                    output,
                    "{} = *({}*)&global_{};\n",
                    c_format_value(to),
                    c_format_type(type_),
                    from.as_ptr() as usize
                )
                .unwrap();
            }
            Instr::Binary {
                op,
                to,
                a,
                b,
                type_: _,
            } => {
                let op_name = match op {
                    BinaryOp::And => "&&",
                    BinaryOp::Or => "||",
                    BinaryOp::Equals => "==",
                    BinaryOp::LargerThanEquals => ">",
                    BinaryOp::LargerThan => ">",
                    BinaryOp::LessThanEquals => "<=",
                    BinaryOp::LessThan => "<",
                    BinaryOp::Add => "+",
                    BinaryOp::Sub => "-",
                    BinaryOp::Mult => "*",
                    BinaryOp::Div => "/",
                    BinaryOp::BitAnd => "&",
                    BinaryOp::BitOr => "|",
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
                    UnaryOp::Dereference | UnaryOp::Reference => unreachable!(),
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
            Instr::Member {
                to,
                of,
                offset: _,
                name,
                size: _,
            } => {
                write!(
                    output,
                    "{} = {}.{};\n",
                    c_format_value(to),
                    c_format_value(of),
                    name
                )
                .unwrap();
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
            Instr::Reference { to, from } => {
                write!(
                    output,
                    "{} = &{};\n",
                    c_format_value(to),
                    c_format_value(from)
                )
                .unwrap();
            }
            Instr::Move {
                to,
                from,
                size: _,
                offset_to_target,
            } => {
                assert_eq!(
                    *offset_to_target, 0,
                    "Offset to target is not done yet in c backend"
                );

                write!(
                    output,
                    "{} = {};\n",
                    c_format_value(to),
                    c_format_value(from)
                )
                .unwrap();
            }
            Instr::MoveIndirect {
                to,
                from,
                size: _,
                offset_to_target,
            } => {
                assert_eq!(
                    *offset_to_target, 0,
                    "Offset to target is not done yet in c backend"
                );

                write!(
                    output,
                    "*{} = {};\n",
                    c_format_value(to),
                    c_format_value(from)
                )
                .unwrap();
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

pub fn append_c_type_headers(output: &mut String) {
    for &type_ in TYPES.lock().iter() {
        if let TypeKind::Empty | TypeKind::Array(_, _) = type_.kind {
            continue;
        }

        output.push_str("typedef ");

        let mut name_is_needed = true;
        match &type_.kind {
            TypeKind::Empty => unreachable!(),
            TypeKind::Array(_, _) => unreachable!(),

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

            TypeKind::Reference(internal) => {
                write!(output, "{} *", c_format_type(*internal)).unwrap()
            }
            TypeKind::Buffer(internal) => {
                write!(
                    output,
                    "struct{{\n  {} *ptr;\n  uint64_t len;\n}}",
                    c_format_type(*internal),
                )
                .unwrap();
            }

            TypeKind::Function {
                args,
                returns,
                is_extern: _,
            } => {
                write!(
                    output,
                    "{} (*t_{}) ",
                    c_format_type_or_void(*returns),
                    type_ as *const _ as usize
                )
                .unwrap();

                output.push('(');
                let mut has_emitted = false;
                for (i, arg) in args.iter().enumerate() {
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
            TypeKind::Struct(_) => todo!(),
        }

        if name_is_needed {
            write!(output, "t_{}", type_ as *const _ as usize).unwrap();
        }

        output.push_str(";\n");
    }
}

pub fn c_format_global(global: usize) -> impl fmt::Display {
    Formatter(move |f| write!(f, "global_{}", global))
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
