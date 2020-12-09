use crate::location::Location;
use std::fmt;
use ustr::{Ustr, UstrMap};

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

impl fmt::Debug for DependencyList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "types: ")?;
        for type_ in self.types.keys() {
            write!(f, "{}, ", type_)?;
        }
        write!(f, " values: ")?;
        for value in self.values.keys() {
            write!(f, "{}, ", value)?;
        }
        Ok(())
    }
}
