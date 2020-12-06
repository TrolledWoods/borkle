// I think using new line characters is cleaner i nthis case because
// there are so many friggin writes.
#![allow(clippy::write_with_newline)]

use crate::ir::{Instr, Routine, Value};
use crate::operators::{BinaryOp, UnaryOp};
use crate::program::Program;
use crate::types::{IntTypeKind, TypeKind, TYPES};
use std::fmt::Write;
use ustr::Ustr;

fn value_to_c(output: &mut String, value: &Value) {
    match value {
        Value::Register(id, _) => write!(output, "reg_{}", id).unwrap(),
        Value::Global(ptr, type_) => write!(
            output,
            "(*({}*)&global_{})",
            type_.c_format(),
            ptr.as_ptr() as usize
        )
        .unwrap(),
    }
}

pub fn declare_constants(output: &mut String, program: &Program) {
    let constant_data = program.constant_data.lock();
    for constant in constant_data.iter() {
        let ptr = constant.ptr.as_ptr();
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

    let constant_data = program.constant_data.lock();
    for constant in constant_data.iter() {
        for (offset, ptr) in constant.constant_pointers.iter() {
            write!(
                output,
                "    global_{}[{}] = &global_{};\n",
                constant.ptr.as_ptr() as usize,
                offset / 8,
                ptr.as_ptr() as usize,
            )
            .unwrap();
        }
    }

    output.push_str("}\n");
}

pub fn routine_to_c(output: &mut String, routine: &Routine, num_args: usize) {
    write!(output, "    // Declare registers\n").unwrap();
    for (i, register) in routine.registers.locals.iter().enumerate() {
        if register.type_.size() != 0 {
            write!(
                output,
                "    {} reg_{}; // {}\n",
                register.type_.c_format(),
                i,
                register.type_
            )
            .unwrap();
        }
    }
    output.push_str("\n    ");

    for i in 0..num_args {
        write!(output, "reg_{0} = arg_{0}; ", i).unwrap();
    }
    output.push_str("\n\n");

    write!(output, "    // Code\n").unwrap();
    for instr in &routine.instr {
        write!(output, "    // {:?}\n", instr).unwrap();
        output.push_str("    ");
        match instr {
            Instr::Call { .. } | Instr::CallExtern { .. } => todo!(),
            Instr::Constant { to, from } => {
                let type_ = to.type_();

                write!(output, "{{uint8_t temp[{}] = {{", type_.size()).unwrap();
                for i in 0..type_.size() {
                    write!(output, "{}, ", unsafe { *from.as_ptr().add(i) }).unwrap();
                }
                write!(output, "}};\n").unwrap();

                output.push_str("    ");
                value_to_c(output, to);
                write!(output, " = *({}*)&temp;}}\n", type_.c_format()).unwrap();
            }
            Instr::Binary {
                op,
                to,
                a,
                b,
                type_,
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

                value_to_c(output, to);
                write!(output, " = ").unwrap();
                value_to_c(output, a);
                write!(output, " {} ", op_name).unwrap();
                value_to_c(output, b);
                write!(output, ";\n").unwrap();
            }
            Instr::Unary { op, to, from } => {
                let op_name = match op {
                    UnaryOp::Negate => "-",
                    UnaryOp::Not => "!",
                    UnaryOp::Dereference | UnaryOp::Reference => unreachable!(),
                };

                value_to_c(output, to);
                write!(output, " = {}", op_name).unwrap();
                value_to_c(output, from);
                write!(output, ";\n").unwrap();
            }
            Instr::Member {
                to,
                of,
                offset: _,
                name,
                size: _,
            } => {
                value_to_c(output, to);
                output.push_str(" = ");
                value_to_c(output, of);
                output.push('.');
                output.push_str(name);
                output.push_str(";\n");
            }
            Instr::Dereference { to, from } => {
                value_to_c(output, to);
                output.push_str(" = *");
                value_to_c(output, from);
                output.push_str(";\n");
            }
            Instr::Reference { to, from } => {
                value_to_c(output, to);
                output.push_str(" = &");
                value_to_c(output, from);
                output.push_str(";\n");
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

                value_to_c(output, to);
                output.push_str(" = ");
                value_to_c(output, from);
                output.push_str(";\n");
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

                output.push('*');
                value_to_c(output, to);
                output.push_str(" = ");
                value_to_c(output, from);
                output.push_str(";\n");
            }
            Instr::JumpIfZero { condition, to } => {
                output.push_str("if (");
                value_to_c(output, condition);
                output.push_str(") ");
                write!(output, "goto label_{};\n", to.0).unwrap();
            }
            Instr::Jump { to } => {
                write!(output, "goto label_{};\n", to.0).unwrap();
            }
            Instr::LabelDefinition(id) => {
                write!(output, "label_{}:;\n", id.0).unwrap();
            }
        }
    }

    output.push_str("    return ");
    value_to_c(output, &routine.result);
    output.push_str(";\n");
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

            TypeKind::Reference(internal) => write!(output, "{} *", internal.c_format()).unwrap(),
            TypeKind::Buffer(internal) => {
                write!(
                    output,
                    "struct{{\n  {} *ptr;\n  uint64_t len;\n}}",
                    internal.c_format()
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
                    returns.c_format(),
                    type_ as *const _ as usize
                )
                .unwrap();

                output.push('(');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        output.push_str(", ");
                    }

                    write!(output, "{}", arg.c_format()).unwrap();
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

pub struct NameMangler {
    prefix: String,
    count: u32,
}

impl NameMangler {
    pub fn new(prefix: String) -> Self {
        Self { prefix, count: 0 }
    }

    pub fn generate(&mut self) -> Ustr {
        let old_len = self.prefix.len();
        write!(&mut self.prefix, "{}", self.count).unwrap();
        self.count += 1;
        let output = (&*self.prefix).into();
        self.prefix.truncate(old_len);
        output
    }
}
