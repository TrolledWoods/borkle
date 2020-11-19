use ustr::{Ustr, UstrSet};

#[derive(Debug)]
pub struct DependencyList {
    values: UstrSet,
    types: UstrSet,
}

impl DependencyList {
    pub fn new() -> Self {
        Self {
            values: UstrSet::default(),
            types: UstrSet::default(),
        }
    }

    pub fn add(&mut self, name: Ustr, kind: DependencyKind) {
        match kind {
            DependencyKind::Value => self.values.insert(name),
            DependencyKind::Type => self.types.insert(name),
        };
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum DependencyKind {
    Type,
    Value,
}
