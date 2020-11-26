#[macro_export]
macro_rules! all_int_types {
    ($type_:expr, $out:expr, ($a:expr, $b:expr), $op:tt) => {{
        match $type_.kind() {
            crate::types::TypeKind::I64 => unsafe {
                let a: i64 = *$a.as_ptr().cast();
                let b: i64 = *$b.as_ptr().cast();
                *$out.as_mut_ptr().cast::<i64>() = a $op b;
            },
            crate::types::TypeKind::U8 => unsafe {
                let a: u8 = *$a.as_ptr().cast();
                let b: u8 = *$b.as_ptr().cast();
                *$out.as_mut_ptr().cast::<u8>() = a $op b;
            }
            _ => unreachable!("Invalid operator combination"),
        }
    }};
}
