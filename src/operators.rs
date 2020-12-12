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

        impl $enum_name {
            #[allow(unused)]
            pub const fn precedence(&self) -> usize {
                match self {
                    $(Self::$operator_name => $precedence,)*
                }
            }
        }

        impl Operator for $enum_name {
            fn from_prefix(string: &str) -> Option<(Self, &'_ str)> {
                $(if let Some(suffix) = string.strip_prefix($name) {
                    return Some((Self::$operator_name, suffix));
                })*

                None
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
    And = ("&&", 1),
    Or  = ("||", 2),

    Equals = ("==", 3),
    NotEquals = ("!=", 3),
    LargerThanEquals = (">=", 3),
    LargerThan = (">", 3),
    LessThanEquals = ("<=", 3),
    LessThan = ("<", 3),

    Add = ("+", 100),
    Sub = ("-", 100),
    Mult = ("*", 101),
    Div = ("/", 102),
    BitAnd = ("&", 4),
    BitOr = ("|", 5),
});

operator!(AccessOp {
    Member = (".", 0),
});

impl BinaryOp {
    fn is_algebraic(self) -> bool {
        matches!(
            self,
            BinaryOp::Add
                | BinaryOp::Sub
                | BinaryOp::Mult
                | BinaryOp::Div
                | BinaryOp::BitAnd
                | BinaryOp::BitOr
        )
    }

    fn is_non_strict_comparison(self) -> bool {
        matches!(
            self,
            BinaryOp::LessThan
                | BinaryOp::LessThanEquals
                | BinaryOp::LargerThan
                | BinaryOp::LargerThanEquals
        )
    }

    fn is_comparison(self) -> bool {
        matches!(
            self,
            BinaryOp::LessThan
                | BinaryOp::LessThanEquals
                | BinaryOp::LargerThan
                | BinaryOp::LargerThanEquals
                | BinaryOp::Equals
                | BinaryOp::NotEquals
        )
    }

    pub fn left_hand_side_from_return(self, returns: Type) -> Option<Type> {
        match (self, returns.kind()) {
            (op, _) if op.is_algebraic() => Some(returns),
            (BinaryOp::And, _) | (BinaryOp::Or, _) => Some(Type::new(TypeKind::Bool)),
            _ => None,
        }
    }

    pub fn right_hand_side_from_left(self, left: Type) -> Option<Type> {
        match (self, left.kind()) {
            (op, TypeKind::Int(_)) | (op, TypeKind::F32) | (op, TypeKind::F64)
                if op.is_algebraic() || op.is_comparison() =>
            {
                Some(left)
            }

            (BinaryOp::Add, TypeKind::Reference(_)) => {
                Some(Type::new(TypeKind::Int(IntTypeKind::Usize)))
            }
            (BinaryOp::Sub, TypeKind::Reference(_)) => {
                Some(Type::new(TypeKind::Int(IntTypeKind::Usize)))
            }

            (BinaryOp::And, _) | (BinaryOp::Or, _) => Some(Type::new(TypeKind::Bool)),
            _ => None,
        }
    }

    pub fn return_from_args(self, left: Type, right: Type) -> Option<Type> {
        match (self, left.kind(), right.kind()) {
            (op, TypeKind::Int(a), TypeKind::Int(b)) if a == b && op.is_algebraic() => Some(left),
            (op, TypeKind::F32, TypeKind::F32) if op.is_algebraic() => Some(left),
            (op, TypeKind::F64, TypeKind::F64) if op.is_algebraic() => Some(left),

            (op, TypeKind::Int(a), TypeKind::Int(b)) if op.is_comparison() && a == b => {
                Some(Type::new(TypeKind::Bool))
            }
            (op, TypeKind::F32, TypeKind::F32) | (op, TypeKind::F64, TypeKind::F64)
                if op.is_non_strict_comparison() =>
            {
                Some(Type::new(TypeKind::Bool))
            }
            (op, TypeKind::Bool, TypeKind::Bool) if op.is_comparison() => {
                Some(Type::new(TypeKind::Bool))
            }

            (BinaryOp::And, TypeKind::Bool, TypeKind::Bool)
            | (BinaryOp::Or, TypeKind::Bool, TypeKind::Bool) => Some(left),

            (BinaryOp::Add, TypeKind::Reference(_), TypeKind::Int(IntTypeKind::Usize))
            | (BinaryOp::Sub, TypeKind::Reference(_), TypeKind::Int(IntTypeKind::Usize)) => {
                Some(left)
            }
            _ => None,
        }
    }

    pub unsafe fn run(self, left: Type, right: Type, a: *const u8, b: *const u8, output: *mut u8) {
        match (self, left.kind(), right.kind()) {
            (BinaryOp::Add, TypeKind::Reference(inner), TypeKind::Int(IntTypeKind::Usize)) => {
                *output.cast() = *a.cast::<usize>() + *b.cast::<usize>() * inner.size();
            }
            (BinaryOp::Sub, TypeKind::Reference(inner), TypeKind::Int(IntTypeKind::Usize)) => {
                *output.cast() = *a.cast::<usize>() - *b.cast::<usize>() * inner.size();
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

            (BinaryOp::And, TypeKind::Bool, TypeKind::Bool) => {
                *output = ((*a > 0) & (*b > 0)) as u8;
            }
            (BinaryOp::Or, TypeKind::Bool, TypeKind::Bool) => {
                *output = ((*a > 0) | (*b > 0)) as u8;
            }

            _ => unreachable!("{:?} does not have an overload for '{}' and '{}', yet somehow it was still attempted to be run", self, left, right),
        }
    }
}
