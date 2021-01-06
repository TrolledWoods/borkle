use crate::location::Location;
use crate::program::{FunctionId, ScopeId};
use std::collections::HashMap;
use std::fmt;
use ustr::{Ustr, UstrMap};

#[derive(Clone)]
pub struct DependencyList {
    pub values: UstrMap<(ScopeId, Location)>,
    pub types: UstrMap<(ScopeId, Location)>,
    pub calling: Vec<FunctionId>,
}

impl DependencyList {
    pub fn new() -> Self {
        Self {
            values: UstrMap::default(),
            types: UstrMap::default(),
            calling: Vec::new(),
        }
    }

    pub fn add(&mut self, loc: Location, scope_id: ScopeId, name: Ustr, kind: DependencyKind) {
        match kind {
            DependencyKind::Value => self.values.insert(name, (scope_id, loc)),
            DependencyKind::Type => self.types.insert(name, (scope_id, loc)),
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
        write!(f, " calling: ")?;
        for calling in &self.calling {
            write!(f, "{:?}", calling)?;
        }
        Ok(())
    }
}
