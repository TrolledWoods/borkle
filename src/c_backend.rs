use crate::ir::{Instr, Routine, Value};
use crate::types::{IntTypeKind, TypeKind, TYPES};
use ustr::Ustr;

pub struct NameMangler {
    prefix: String,
    count: u32,
}

impl NameMangler {
    pub fn new(prefix: String) -> Self {
        Self { prefix, count: 0 }
    }

    pub fn generate(&mut self) -> Ustr {
        use std::fmt::Write;

        let old_len = self.prefix.len();
        write!(&mut self.prefix, "{}", self.count).unwrap();
        self.count += 1;
        let output = (&*self.prefix).into();
        self.prefix.truncate(old_len);
        output
    }
}

pub fn routine_to_c(output: &mut String, routine: &Routine) {
    for instr in &routine.instr {
        match instr {
            Instr::Call { .. } | Instr::CallExtern { .. } => todo!(),
            Instr::Constant { to, from } => {}
        }
    }
}

pub fn append_c_type_headers(output: &mut String) {
    for &type_ in TYPES.lock().iter() {
        if let TypeKind::Empty | TypeKind::Array(_, _) = type_.kind {
            continue;
        }

        use std::fmt::Write;

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
            TypeKind::Int(IntTypeKind::Usize) => output.push_str("size_t "),
            TypeKind::Int(IntTypeKind::Isize) => output.push_str("ssize_t "),

            TypeKind::F32 => output.push_str("float "),
            TypeKind::F64 => output.push_str("double "),

            TypeKind::Reference(internal) => write!(output, "{} *", internal.c_format()).unwrap(),
            TypeKind::Buffer(internal) => {
                write!(
                    output,
                    "struct{{\n  {} *ptr,\n  size_t len\n}}",
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
