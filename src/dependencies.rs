use crate::location::Location;
use ustr::{Ustr, UstrMap};

#[derive(Debug)]
pub struct DependencyList {
    pub values: UstrMap<Location>,
    pub types: UstrMap<Location>,
}

impl DependencyList {
    pub fn new() -> Self {
        Self {
            values: UstrMap::default(),
            types: UstrMap::default(),
        }
    }

    pub fn add(&mut self, loc: Location, name: Ustr, kind: DependencyKind) {
        match kind {
            DependencyKind::Value => self.values.insert(name, loc),
            DependencyKind::Type => self.types.insert(name, loc),
        };
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum DependencyKind {
    Type,
    Value,
}
