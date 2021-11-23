use crate::types::{IntTypeKind, Type, TypeKind};

macro_rules! all_int_types {
    ($int_kind:expr, $out:expr, ($a:expr, $b:expr), $op:tt) => {{
        match $int_kind {
            crate::types::IntTypeKind::Isize => {
                let a: isize = *$a.cast();
                let b: isize = *$b.cast();
                *$out.cast() = a $op b;
            },
            crate::types::IntTypeKind::Usize => {
                let a: usize = *$a.cast();
                let b: usize = *$b.cast();
                *$out.cast() = a $op b;
            },
            crate::types::IntTypeKind::I64 => {
                let a: i64 = *$a.cast();
                let b: i64 = *$b.cast();
                *$out.cast() = a $op b;
            },
            crate::types::IntTypeKind::U64 => {
                let a: u64 = *$a.cast();
                let b: u64 = *$b.cast();
                *$out.cast() = a $op b;
            },
            crate::types::IntTypeKind::I32 => {
                let a: i32 = *$a.cast();
                let b: i32 = *$b.cast();
                *$out.cast() = a $op b;
            },
            crate::types::IntTypeKind::U32 => {
                let a: u32 = *$a.cast();
                let b: u32 = *$b.cast();
                *$out.cast() = a $op b;
            },
            crate::types::IntTypeKind::I16 => {
                let a: i16 = *$a.cast();
                let b: i16 = *$b.cast();
                *$out.cast() = a $op b;
            },
            crate::types::IntTypeKind::U16 => {
                let a: u16 = *$a.cast();
                let b: u16 = *$b.cast();
                *$out.cast() = a $op b;
            },
            crate::types::IntTypeKind::I8 => {
                let a: i8 = *$a.cast();
                let b: i8 = *$b.cast();
                *$out.cast() = a $op b;
            }
            crate::types::IntTypeKind::U8 => {
                let a: u8 = *$a.cast();
                let b: u8 = *$b.cast();
                *$out.cast() = a $op b;
            }
        }
    }};
}

pub trait Operator: Sized {
    fn from_prefix(string: &str) -> Option<(Self, &'_ str)>;
    fn precedence(&self) -> usize;
}

macro_rules! operator {
    ($enum_name:ident {
        $(
            $operator_name:ident = ($name:literal, $precedence:literal),
        )*
    }) => {
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        pub enum $enum_name {
            $($operator_name,)*
        }

        impl Operator for $enum_name {
            fn from_prefix(string: &str) -> Option<(Self, &'_ str)> {
                $(if let Some(suffix) = string.strip_prefix($name) {
                    return Some((Self::$operator_name, suffix));
                })*

                None
            }

            fn precedence(&self) -> usize {
                match self {
                    $(Self::$operator_name => $precedence,)*
                }
            }
        }
    };
}

operator!(UnaryOp {
    AutoCast = ("<<", 0),
    Negate = ("-", 0),
    Not = ("!", 0),
    Reference = ("&", 0),
    Dereference = ("*", 0),
});

operator!(BinaryOp {
    TypeBound = (":", 2),

    And = ("&&", 6),
    Or  = ("||", 6),
    Range = ("..", 48539),

    Equals = ("==", 8),
    NotEquals = ("!=", 8),
    LargerThanEquals = (">=", 8),
    LargerThan = (">", 8),
    LessThanEquals = ("<=", 8),
    LessThan = ("<", 8),

    Add = ("+", 100),
    Sub = ("-", 100),
    Mult = ("*", 101),
    Div = ("/", 101),
    BitAnd = ("&", 7),
    BitOr = ("|", 7),

    Assign = ("=", 1),
});

operator!(AccessOp {
    Member = (".", 0),
});

const INT_OPERATIONS: &[[TypeKind; 3]] = &[
    [
        TypeKind::Int(IntTypeKind::U8),
        TypeKind::Int(IntTypeKind::U8),
        TypeKind::Int(IntTypeKind::U8),
    ],
    [
        TypeKind::Int(IntTypeKind::U16),
        TypeKind::Int(IntTypeKind::U16),
        TypeKind::Int(IntTypeKind::U16),
    ],
    [
        TypeKind::Int(IntTypeKind::U32),
        TypeKind::Int(IntTypeKind::U32),
        TypeKind::Int(IntTypeKind::U32),
    ],
    [
        TypeKind::Int(IntTypeKind::U64),
        TypeKind::Int(IntTypeKind::U64),
        TypeKind::Int(IntTypeKind::U64),
    ],
    [
        TypeKind::Int(IntTypeKind::I8),
        TypeKind::Int(IntTypeKind::I8),
        TypeKind::Int(IntTypeKind::I8),
    ],
    [
        TypeKind::Int(IntTypeKind::I16),
        TypeKind::Int(IntTypeKind::I16),
        TypeKind::Int(IntTypeKind::I16),
    ],
    [
        TypeKind::Int(IntTypeKind::I32),
        TypeKind::Int(IntTypeKind::I32),
        TypeKind::Int(IntTypeKind::I32),
    ],
    [
        TypeKind::Int(IntTypeKind::I64),
        TypeKind::Int(IntTypeKind::I64),
        TypeKind::Int(IntTypeKind::I64),
    ],
    [
        TypeKind::Int(IntTypeKind::Isize),
        TypeKind::Int(IntTypeKind::Isize),
        TypeKind::Int(IntTypeKind::Isize),
    ],
    [
        TypeKind::Int(IntTypeKind::Usize),
        TypeKind::Int(IntTypeKind::Usize),
        TypeKind::Int(IntTypeKind::Usize),
    ],
];

const POINTER_OPERATIONS: &[[TypeKind; 3]] = &[
    [
        TypeKind::VoidPtr,
        TypeKind::Int(IntTypeKind::Usize),
        TypeKind::VoidPtr,
    ],
    [
        TypeKind::VoidPtr,
        TypeKind::Int(IntTypeKind::Isize),
        TypeKind::VoidPtr,
    ],
];

const BOOLEAN_COMPARISONS: &[[TypeKind; 3]] = &[
    [
        TypeKind::Int(IntTypeKind::U8),
        TypeKind::Int(IntTypeKind::U8),
        TypeKind::Bool,
    ],
    [
        TypeKind::Int(IntTypeKind::U16),
        TypeKind::Int(IntTypeKind::U16),
        TypeKind::Bool,
    ],
    [
        TypeKind::Int(IntTypeKind::U32),
        TypeKind::Int(IntTypeKind::U32),
        TypeKind::Bool,
    ],
    [
        TypeKind::Int(IntTypeKind::U64),
        TypeKind::Int(IntTypeKind::U64),
        TypeKind::Bool,
    ],
    [
        TypeKind::Int(IntTypeKind::I8),
        TypeKind::Int(IntTypeKind::I8),
        TypeKind::Bool,
    ],
    [
        TypeKind::Int(IntTypeKind::I16),
        TypeKind::Int(IntTypeKind::I16),
        TypeKind::Bool,
    ],
    [
        TypeKind::Int(IntTypeKind::I32),
        TypeKind::Int(IntTypeKind::I32),
        TypeKind::Bool,
    ],
    [
        TypeKind::Int(IntTypeKind::I64),
        TypeKind::Int(IntTypeKind::I64),
        TypeKind::Bool,
    ],
    [
        TypeKind::Int(IntTypeKind::Isize),
        TypeKind::Int(IntTypeKind::Isize),
        TypeKind::Bool,
    ],
    [
        TypeKind::Int(IntTypeKind::Usize),
        TypeKind::Int(IntTypeKind::Usize),
        TypeKind::Bool,
    ],
];

const BOOLEAN_META_OPERATORS: &[[TypeKind; 3]] =
    &[[TypeKind::Bool, TypeKind::Bool, TypeKind::Bool]];

fn check_operations<'a>(
    matching_operators: impl Iterator<Item = &'a [TypeKind; 3]> + Clone,
    givens: [Option<Type>; 3],
) -> Result<[Option<Type>; 3], ()> {
    let mut ops = matching_operators.filter(|a| {
        a.iter()
            .zip(&givens)
            .map(|(a, b)| b.map_or(true, |b| a == b.kind()))
            .all(|v| v == true)
    });
    let output = ops.next().ok_or(())?;

    // The answer has to be unanimous(all output have to give the specific type), for the inferrence to
    // happen.
    let mut i = 0;
    Ok(output.clone().map(|out| {
        let out = ops.clone().all(|v| v[i] == out).then(|| Type::new(out));
        i += 1;
        out
    }))
}

impl BinaryOp {
    pub fn try_infer_types(self, givens: [Option<Type>; 3]) -> Result<[Option<Type>; 3], ()> {
        /* This is not valid, since if all the types in the inputs/outputs are known, this will never fail, even though
         * the operation may not actually support those inputs/outputs. It would be nice to be able to do this shortcut
         * without that incorrectness.
            if let Some(given) = givens[wanted as usize] {
                return InferredType::Found(given);
            }
        */

        match self {
            BinaryOp::Add | BinaryOp::Sub => {
                check_operations(INT_OPERATIONS.iter().chain(POINTER_OPERATIONS), givens)
            }
            BinaryOp::Mult | BinaryOp::Div => check_operations(INT_OPERATIONS.iter(), givens),
            BinaryOp::BitAnd | BinaryOp::BitOr => {
                check_operations(INT_OPERATIONS.iter().chain(BOOLEAN_META_OPERATORS), givens)
            }
            BinaryOp::Equals | BinaryOp::NotEquals => check_operations(
                BOOLEAN_COMPARISONS.iter().chain(BOOLEAN_META_OPERATORS),
                givens,
            ),
            BinaryOp::LargerThanEquals
            | BinaryOp::LargerThan
            | BinaryOp::LessThanEquals
            | BinaryOp::LessThan => check_operations(BOOLEAN_COMPARISONS.iter(), givens),
            _ => unimplemented!("Operator not finished yet"),
        }
    }

    pub fn is_right_to_left(self) -> bool {
        matches!(self, BinaryOp::Assign)
    }

    pub unsafe fn run(self, left: Type, right: Type, a: *const u8, b: *const u8, output: *mut u8) {
        match (self, left.kind(), right.kind()) {
            (BinaryOp::Add, TypeKind::Reference { pointee, .. }, TypeKind::Int(IntTypeKind::Usize)) => {
                *output.cast() = *a.cast::<usize>() + *b.cast::<usize>() * pointee.size();
            }
            (BinaryOp::Sub, TypeKind::Reference { pointee, .. }, TypeKind::Int(IntTypeKind::Usize)) => {
                *output.cast() = *a.cast::<usize>() - *b.cast::<usize>() * pointee.size();
            }

            (BinaryOp::Add, TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => {
                all_int_types!(i1, output, (a, b), +)
            }
            (BinaryOp::Add, TypeKind::F32, TypeKind::F32) => {
                *output.cast() = *a.cast::<f32>() + *b.cast::<f32>();
            }
            (BinaryOp::Add, TypeKind::F64, TypeKind::F64) => {
                *output.cast() = *a.cast::<f64>() + *b.cast::<f64>();
            }

            (BinaryOp::Sub, TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => {
                all_int_types!(i1, output, (a, b), -)
            }
            (BinaryOp::Sub, TypeKind::F32, TypeKind::F32) => {
                *output.cast() = *a.cast::<f32>() - *b.cast::<f32>();
            }
            (BinaryOp::Sub, TypeKind::F64, TypeKind::F64) => {
                *output.cast() = *a.cast::<f64>() - *b.cast::<f64>();
            }

            (BinaryOp::Mult, TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => {
                all_int_types!(i1, output, (a, b), *)
            }
            (BinaryOp::Mult, TypeKind::F32, TypeKind::F32) => {
                *output.cast() = *a.cast::<f32>() * *b.cast::<f32>();
            }
            (BinaryOp::Mult, TypeKind::F64, TypeKind::F64) => {
                *output.cast() = *a.cast::<f64>() * *b.cast::<f64>();
            }

            (BinaryOp::Div, TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => {
                all_int_types!(i1, output, (a, b), /)
            }
            (BinaryOp::Div, TypeKind::F32, TypeKind::F32) => {
                *output.cast() = *a.cast::<f32>() / *b.cast::<f32>();
            }
            (BinaryOp::Div, TypeKind::F64, TypeKind::F64) => {
                *output.cast() = *a.cast::<f64>() / *b.cast::<f64>();
            }

            (BinaryOp::BitAnd, TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => {
                all_int_types!(i1, output, (a, b), &)
            }

            (BinaryOp::BitOr, TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => {
                all_int_types!(i1, output, (a, b), |)
            }

            (BinaryOp::Equals, TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 =>
                all_int_types!(i1, output, (a, b), ==),
            (BinaryOp::NotEquals, TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => {
                all_int_types!(i1, output, (a, b), !=)
            }

            (BinaryOp::Equals, TypeKind::Type, TypeKind::Type) => {
                *output.cast() = *a.cast::<usize>() == *b.cast::<usize>();
            },
            (BinaryOp::NotEquals, TypeKind::Type, TypeKind::Type) => {
                *output.cast() = *a.cast::<usize>() != *b.cast::<usize>();
            },

            (BinaryOp::Equals, TypeKind::Reference { pointee: i1, .. }, TypeKind::Reference { pointee: i2, .. }) if i1 == i2 =>
                *output.cast() = *a.cast::<*const u8>() == *b.cast::<*const u8>(),
            (BinaryOp::NotEquals, TypeKind::Reference { pointee: i1, .. }, TypeKind::Reference { pointee: i2, .. }) if i1 == i2 =>
                *output.cast() = *a.cast::<*const u8>() != *b.cast::<*const u8>(),
            (BinaryOp::LessThan, TypeKind::Reference { pointee: i1, .. }, TypeKind::Reference { pointee: i2, .. }) if i1 == i2 =>
                *output.cast() = *a.cast::<*const u8>() < *b.cast::<*const u8>(),
            (BinaryOp::LessThan, TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => {
                all_int_types!(i1, output, (a, b), <)
            }
            (BinaryOp::LessThan, TypeKind::F32, TypeKind::F32) =>
                *output.cast() = *a.cast::<f32>() < *b.cast::<f32>(),
            (BinaryOp::LessThan, TypeKind::F64, TypeKind::F64) =>
                *output.cast() = *a.cast::<f64>() < *b.cast::<f64>(),

            (BinaryOp::LessThanEquals, TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => {
                all_int_types!(i1, output, (a, b), <=)
            }
            (BinaryOp::LessThanEquals, TypeKind::F32, TypeKind::F32) =>
                *output.cast() = *a.cast::<f32>() <= *b.cast::<f32>(),
            (BinaryOp::LessThanEquals, TypeKind::F64, TypeKind::F64) =>
                *output.cast() = *a.cast::<f64>() <= *b.cast::<f64>(),

            (BinaryOp::LargerThan, TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => {
                all_int_types!(i1, output, (a, b), >)
            }
            (BinaryOp::LargerThan, TypeKind::F32, TypeKind::F32) =>
                *output.cast() = *a.cast::<f32>() > *b.cast::<f32>(),
            (BinaryOp::LargerThan, TypeKind::F64, TypeKind::F64) =>
                *output.cast() = *a.cast::<f64>() > *b.cast::<f64>(),

            (BinaryOp::LargerThanEquals, TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => {
                all_int_types!(i1, output, (a, b), >=)
            }
            (BinaryOp::LargerThanEquals, TypeKind::F32, TypeKind::F32) =>
                *output.cast() = *a.cast::<f32>() >= *b.cast::<f32>(),
            (BinaryOp::LargerThanEquals, TypeKind::F64, TypeKind::F64) =>
                *output.cast() = *a.cast::<f64>() >= *b.cast::<f64>(),

            (BinaryOp::Range, _, _) => {
                std::ptr::copy(a, output, left.size());
                let offset = crate::types::to_align(left.size(), left.align());
                std::ptr::copy(b, output.add(offset), left.size());
            }

            (BinaryOp::And, TypeKind::Bool, TypeKind::Bool) => {
                *output = ((*a > 0) && (*b > 0)) as u8;
            }
            (BinaryOp::Or, TypeKind::Bool, TypeKind::Bool) => {
                *output = ((*a > 0) || (*b > 0)) as u8;
            }

            _ => unreachable!("{:?} does not have an overload for '{}' and '{}', yet somehow it was still attempted to be run", self, left, right),
        }
    }
}
