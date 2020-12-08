#[macro_export]
macro_rules! all_int_types {
    ($int_kind:expr, $out:expr, ($a:expr, $b:expr), $op:tt) => {{
        match $int_kind {
            crate::types::IntTypeKind::Isize => unsafe {
                let a: isize = *$a.as_ptr().cast();
                let b: isize = *$b.as_ptr().cast();
                *$out.as_mut_ptr().cast() = a $op b;
            },
            crate::types::IntTypeKind::Usize => unsafe {
                let a: usize = *$a.as_ptr().cast();
                let b: usize = *$b.as_ptr().cast();
                *$out.as_mut_ptr().cast() = a $op b;
            },
            crate::types::IntTypeKind::I64 => unsafe {
                let a: i64 = *$a.as_ptr().cast();
                let b: i64 = *$b.as_ptr().cast();
                *$out.as_mut_ptr().cast() = a $op b;
            },
            crate::types::IntTypeKind::U64 => unsafe {
                let a: u64 = *$a.as_ptr().cast();
                let b: u64 = *$b.as_ptr().cast();
                *$out.as_mut_ptr().cast() = a $op b;
            },
            crate::types::IntTypeKind::I32 => unsafe {
                let a: i32 = *$a.as_ptr().cast();
                let b: i32 = *$b.as_ptr().cast();
                *$out.as_mut_ptr().cast() = a $op b;
            },
            crate::types::IntTypeKind::U32 => unsafe {
                let a: u32 = *$a.as_ptr().cast();
                let b: u32 = *$b.as_ptr().cast();
                *$out.as_mut_ptr().cast() = a $op b;
            },
            crate::types::IntTypeKind::I16 => unsafe {
                let a: i16 = *$a.as_ptr().cast();
                let b: i16 = *$b.as_ptr().cast();
                *$out.as_mut_ptr().cast() = a $op b;
            },
            crate::types::IntTypeKind::U16 => unsafe {
                let a: u16 = *$a.as_ptr().cast();
                let b: u16 = *$b.as_ptr().cast();
                *$out.as_mut_ptr().cast() = a $op b;
            },
            crate::types::IntTypeKind::I8 => unsafe {
                let a: i8 = *$a.as_ptr().cast();
                let b: i8 = *$b.as_ptr().cast();
                *$out.as_mut_ptr().cast() = a $op b;
            }
            crate::types::IntTypeKind::U8 => unsafe {
                let a: u8 = *$a.as_ptr().cast();
                let b: u8 = *$b.as_ptr().cast();
                *$out.as_mut_ptr().cast() = a $op b;
            }
        }
    }};
}
