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
            match type_.kind() {
                TypeKind::Int(int_kind) => {
                    let size = int_kind.size_align().0;

                    let mut big_int = [0; 16];
                    unsafe {
                        std::ptr::copy_nonoverlapping(ptr.as_ptr(), big_int.as_mut_ptr(), size);
                    }

                    if int_kind.signed() && (big_int[size] & 0x80) > 0 {
                        big_int[size + 1..].fill(0xff);
                    }

                    write!(
                        f,
                        "{}",
                        i128::from_le_bytes(big_int),
                    )?;
                }
                _ => {
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
        write!(output, "}};\n").unwrap();
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
                        "    {} reg_{};\n",
                        c_format_type(register.type_),
                        i,
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
                            write!(output, "{} = ", c_format_value(to)).unwrap();
                        }

                        if let Value::Global(ptr, _) = pointer {
                            let function_id = unsafe { *ptr.as_ptr().cast::<FunctionId>() };
                            write!(output, "function_{}(", usize::from(function_id))
                            .unwrap();
                        } else {
                            write!(
                                output,
                                "({}.inner)(",
                                c_format_value(pointer),
                            )
                            .unwrap();
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
                        if matches!(value.type_().kind(), TypeKind::Reference { .. }) {
                            write!(output, "{0}.inner = {0}.inner + 1;\n", c_format_value(value)).unwrap();
                        } else {
                            write!(output, "{0} = {0} + 1;\n", c_format_value(value)).unwrap();
                        }
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
                        let is_pointer_op = matches!(a.type_().kind(), TypeKind::Reference { .. });

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

                        if is_pointer_op {
                            // @HACK: To support pointer arithmetic for now
                            let rhs_is_ptr = matches!(b.type_().kind(), TypeKind::Reference { .. });
                            let ret_is_ptr = matches!(to.type_().kind(), TypeKind::Reference { .. });

                            write!(
                                output,
                                "{}{} = {}.inner {} {}{};\n",
                                c_format_value(to),
                                if ret_is_ptr { ".inner" } else { "" },
                                c_format_value(a),
                                op_name,
                                c_format_value(b),
                                if rhs_is_ptr { ".inner" } else { "" },
                            )
                            .unwrap();
                        } else {
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
                        write!(output, "{} = ", c_format_value(to)).unwrap();

                        c_output_member(output, of, *member);

                        write!(output, ";\n").unwrap();
                    }
                    Instr::PointerToMemberOfPointer { to, of, member } => {
                        write!(
                            output,
                            "{}.inner = &(",
                            c_format_value(to),
                        )
                        .unwrap();
                        c_output_to_special_member(output, of, of.type_().pointing_to().unwrap(), "(*", ".inner)", *member);
                        output.push_str(");\n");
                    }
                    Instr::Dereference { to, from } => {
                        write!(
                            output,
                            "{} = *{}.inner;\n",
                            c_format_value(to),
                            c_format_value(from)
                        )
                        .unwrap();
                    }
                    Instr::PointerToMemberOfValue { to, from, offset } => {
                        write!(output, "{}.inner = &", c_format_value(to))
                            .unwrap();

                        c_output_member(output, from, *offset);

                        output.push_str(";\n");
                    }
                    Instr::BitCast {
                        to,
                        from,
                    } => {
                        write!(output, "{} = *({}*)&{};\n", c_format_value(to), c_format_type(to.type_()), c_format_value(from)).unwrap();
                    }
                    Instr::MoveToMemberOfValue {
                        to,
                        from,
                        size: _,
                        member,
                    } => {
                        c_output_member(output, to, *member);

                        write!(output, " = {};\n", c_format_value(from)).unwrap();
                    }
                    Instr::MoveToMemberOfPointer {
                        to,
                        from,
                        size: _,
                        member,
                    } => {
                        c_output_to_special_member(output, to, to.type_().pointing_to().unwrap(), "(*", ".inner)", *member);

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
                "{} = fwrite({}.inner, 1, {}.len, stdout);\n",
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
                        {0}.inner = malloc({0}.len);
                        memcpy({0}.inner, temp_data, {0}.len);
                    }}\n",
                c_format_value(&to),
            )
            .unwrap();
        }
        BuiltinFunction::Alloc => {
            write!(
                output,
                "{}.inner = malloc({});\n",
                c_format_value(&to),
                c_format_value(&args[0]),
            )
            .unwrap();
        }
        BuiltinFunction::Dealloc => {
            write!(output, "free({}.inner);\n", c_format_value(&args[0])).unwrap();
        }
        BuiltinFunction::MemCopy => {
            write!(
                output,
                "memmove({}.inner, {}.inner, {});\n",
                c_format_value(&args[1]),
                c_format_value(&args[0]),
                c_format_value(&args[2])
            )
            .unwrap();
        }
        BuiltinFunction::MemCopyNonOverlapping => {
            write!(
                output,
                "memcpy({}.inner, {}.inner, {});\n",
                c_format_value(&args[1]),
                c_format_value(&args[0]),
                c_format_value(&args[2])
            )
            .unwrap();
        }
    }
}

/// "trivial" types are just printed inline, and no structs are created for them, to spare some sanity
fn is_type_trivial(type_: Type) -> bool {
    matches!(type_.kind(), TypeKind::Int(_) | TypeKind::Bool | TypeKind::F32 | TypeKind::F64 | TypeKind::Type)
}

/// Returns the name of a type, designed to be human readable so we can descipher the c-code somewhat
/// easily.
/// For trivial types, this just returns the type-definition as it would be in C, for non-trivial types,
/// it's expected that the caller appends a `struct` keyword before the type(or it may be used to define the type itself).
fn name_of_type(mut out: impl Write, type_: Type, rec: u32) -> fmt::Result {
    fn fallback_name(mut out: impl Write, type_: Type) -> fmt::Result {
        out.write_char('_')?;
        let mut number = type_.0 as *const _ as usize;
        while number > 0 {
            let value = (number % 36) as u32;
            number /= 36;
            out.write_char(char::from_digit(value, 36).unwrap())?;
        }

        Ok(())
    }
    
    if rec > 2 {
        return fallback_name(out, type_);
    }

    match *type_.kind() {
        TypeKind::Int(int_kind) => match int_kind {
            IntTypeKind::I8    => out.write_str("i8")?,
            IntTypeKind::I16   => out.write_str("i16")?,
            IntTypeKind::I32   => out.write_str("i32")?,
            IntTypeKind::I64   => out.write_str("i64")?,
            IntTypeKind::Isize => out.write_str("isize")?,
            IntTypeKind::U8    => out.write_str("u8")?,
            IntTypeKind::U16   => out.write_str("u16")?,
            IntTypeKind::U32   => out.write_str("u32")?,
            IntTypeKind::U64   => out.write_str("u64")?,
            IntTypeKind::Usize => out.write_str("usize")?,
        },
        TypeKind::Bool => out.write_str("bool")?,

        // Non-trivial types
        TypeKind::Array(element, size) => {
            write!(out, "arr{}_", size)?;
            name_of_type(out, element, rec + 1)?;
        }
        TypeKind::Reference { pointee, permits } => {
            out.write_str("ref_")?;
            out.write_str(permits.to_str())?;
            out.write_char('_')?;
            name_of_type(out, pointee, rec + 1)?;
        }
        TypeKind::Buffer { pointee, permits } => {
            out.write_str("buf_")?;
            out.write_str(permits.to_str())?;
            out.write_char('_')?;
            name_of_type(out, pointee, rec + 1)?;
        }
        TypeKind::Struct { .. } => {
            out.write_str("struct")?;
            fallback_name(out, type_)?;
        }
        TypeKind::Function { .. } => {
            out.write_str("fn")?;
            fallback_name(out, type_)?;
        }

        _ => todo!(),
    }

    Ok(())
}

pub fn declare_types(output: &mut String) {
    let types = TYPES.lock();

    // Declare the types
    for &type_ in &*types {
        if type_.size == 0 || is_type_trivial(Type(type_)) {
            continue;
        }

        output.push_str("struct ");
        name_of_type(&mut *output, Type(type_), 0).unwrap();
        output.push_str(";\n");
    }

    // Define the types
    for type_ in &*types {
        if type_.size == 0 || is_type_trivial(Type(type_)) {
            continue;
        }

        output.push_str("struct ");
        name_of_type(&mut *output, Type(type_), 0).unwrap();
        output.push_str(" { ");

        match type_.kind {
            TypeKind::Array(internal, len) => {
                write!(output, "{} inner[{}]; ", c_format_type(internal), len).unwrap();
            }
            TypeKind::Reference { pointee, .. } => {
                if pointee.size() == 0 {
                    output.push_str("void *inner;");
                } else {
                    write!(output, "{} *inner; ", c_format_type(pointee)).unwrap();
                }
            }
            TypeKind::Buffer { pointee, .. } => {
                write!(output, "{} *inner; usize len; ", c_format_type(pointee)).unwrap();
            }
            TypeKind::Struct(ref fields) => {
                for &(name, arg_type) in fields {
                    if arg_type.size() == 0 { continue; }

                    output.push_str("\n\t");
                    write!(output, "{} {};", c_format_type(arg_type), name).unwrap();
                }
            }
            TypeKind::Function { ref args, returns } => {
                write!(output, "{} (*inner)(", c_format_type_or_void(returns)).unwrap();

                for (i, &arg) in args.iter().filter(|v| v.size() > 0).enumerate() {
                    if i > 0 { output.push_str(", "); }

                    write!(output, "{}", c_format_type(arg)).unwrap();
                }

                output.push_str(");");
            }
            _ => unreachable!(),
        }

        output.push_str(" };\n");
    }

    drop(types);
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

/// Formats a type as C. The type can't be zero sized.
pub fn c_format_type(type_: Type) -> impl fmt::Display {
    debug_assert_ne!(type_.size(), 0);

    Formatter(move |f| {
        if is_type_trivial(type_) {
            name_of_type(f, type_, 0)
        } else {
            f.write_str("struct ")?;
            name_of_type(f, type_, 0)
        }
    })
}

/// Formats a type as C. If the type is zero sized, it uses void instead
pub fn c_format_type_or_void(type_: Type) -> impl fmt::Display {
    Formatter(move |f| {
        if type_.size() == 0 {
            write!(f, "void")
        } else {
            write!(f, "{}", c_format_type(type_))
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

fn c_output_member(output: &mut String, value: &Value, member: crate::ir::Member) {
    c_output_to_special_member(output, value, value.type_(), "", "", member);
}

fn c_output_to_special_member(output: &mut String, value: &Value, mut type_: Type, value_prefix: &str, value_suffix: &str, member: crate::ir::Member) {
    let mut offset = member.offset;

    // @Speed!!!
    let mut members = Vec::with_capacity(member.amount);
    'outer_loop: for _ in 0..member.amount {
        for &(name, member_offset, member_type) in type_.0.members.iter().rev() {
            if offset >= member_offset {
                members.push((name, type_, member_type));

                offset -= member_offset;
                type_ = member_type;
                continue 'outer_loop;
            }
        }

        unreachable!("No member found, this shouldn't happen");
    }

    for &(name, base_type, member_type) in members.iter().rev() {
        match (base_type.kind(), &*name) {
            (TypeKind::Buffer { .. }, "ptr") => {
                write!(output, "(*({}*)&", c_format_type(member_type)).unwrap();
            }
            _ => {}
        }
    }

    write!(output, "{}{}{}", value_prefix, c_format_value(value), value_suffix).unwrap();

    for &(name, base_type, _) in members.iter() {
        match (base_type.kind(), &*name) {
            (TypeKind::Buffer { .. }, "ptr") => {
                output.push_str(".inner)");
            }
            _ => {
                write!(output, ".{}", name).unwrap();
            }
        }
    }
}

pub const BOILER_PLATE: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>

typedef uint8_t  bool;
typedef int8_t   i8;
typedef int16_t  i16;
typedef int32_t  i32;
typedef int64_t  i64;
typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
typedef int64_t  isize;
typedef uint64_t usize;

"#;

