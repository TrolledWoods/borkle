use bumpalo::Bump;
use lazy_static::lazy_static;
use parking_lot::Mutex;
use std::borrow::Borrow;
use std::collections::HashSet;
use std::sync::Arc;

lazy_static! {
    static ref TYPES: Mutex<HashSet<&'static TypeData>> = Mutex::new(HashSet::new());
}

#[derive(Clone, Copy, Hash)]
pub struct Type(&'static TypeData);

impl From<TypeKind> for Type {
    fn from(other: TypeKind) -> Self {
        Self::new(other)
    }
}

impl Type {
    pub fn new(kind: TypeKind) -> Self {
        let (size, align) = kind.calculate_size_align();

        let data = TypeData { size, align, kind };
        let mut types = TYPES.lock();
        if let Some(content) = types.get(&data) {
            Self(content)
        } else {
            let leaked = Box::leak(Box::new(data));
            types.insert(leaked);
            Self(leaked)
        }
    }
}

#[derive(Hash, PartialEq, Eq)]
struct TypeData {
    size: usize,
    align: usize,
    kind: TypeKind,
}

#[derive(Hash, PartialEq, Eq)]
pub enum TypeKind {
    F64,
    I64,
}

impl TypeKind {
    const fn calculate_size_align(&self) -> (usize, usize) {
        match self {
            Self::F64 | Self::I64 => (8, 8),
        }
    }
}
