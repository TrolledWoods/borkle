use crate::location::Location;
use crate::program::{FunctionId, ScopeId};
use std::collections::HashMap;
use std::fmt;
use ustr::{Ustr, UstrMap};

pub struct DependencyList {
    pub values: UstrMap<(ScopeId, Location)>,
    pub types: UstrMap<(ScopeId, Location)>,
    pub callables: HashMap<FunctionId, Location>,
}

impl DependencyList {
    pub fn new() -> Self {
        Self {
            values: UstrMap::default(),
            types: UstrMap::default(),
            callables: HashMap::default(),
        }
    }

    pub fn add(&mut self, loc: Location, scope_id: ScopeId, name: Ustr, kind: DependencyKind) {
        match kind {
            DependencyKind::Value => self.values.insert(name, (scope_id, loc)),
            DependencyKind::Type => self.types.insert(name, (scope_id, loc)),
        };
    }

    pub fn add_function(&mut self, loc: Location, function_id: FunctionId) {
        self.callables.insert(function_id, loc);
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
