use crate::errors::ErrorCtx;
use crate::location::Location;
use parking_lot::RwLock;
use std::collections::{HashMap, HashSet};
use ustr::{Ustr, UstrMap};

#[derive(Clone, Copy, Debug)]
pub struct ScopeId(u32);

pub struct ScopeContext {
    scope_id_ctr: u32,
    // FIXME: This is not a very concurrent datastructure, but I do not have the
    // brainpower to figure out exactly how to do this, so this'll be fine for now.
    scopes: RwLock<HashMap<ScopeId, Scope>>,
}

impl ScopeContext {
    pub fn new() -> Self {
        Self {
            scope_id_ctr: 0,
            scopes: RwLock::new(HashMap::new()),
        }
    }

    pub fn insert_dependencies(&self, deps: DependencyList) {}

    pub fn insert(&self, scope: ScopeId, name: Ustr, resource: ResourceId) {}
}

pub enum Dependency {
    Type(ResourceId),
}

pub struct DependencyList {
    // FIXME: This is a stupid disgrace of a datastructure, DON'T do this.
    dependencies: HashSet<(Dependency, Vec<Ustr>)>,
    temp: Vec<Ustr>,
    scope: ScopeId,
}

impl DependencyList {
    pub fn new(scope: ScopeId) -> Self {
        Self {
            dependencies: HashSet::new(),
            temp: Vec::new(),
            scope,
        }
    }

    pub fn add_type(&mut self, name: Ustr) {
        self.temp.push(name);
    }

    pub fn emit_type(&mut self, resource: ResourceId) {
        let dep = Dependency::Type(resource);
        if !self.dependencies.contains((dep, self.temp.as_slice())) {
            self.dependencies.insert((dep, self.temp.clone()));
        }

        self.temp.clear();
    }
}

struct Scope {
    name: Ustr,
    loc: Option<Location>,

    wildcards: Vec<ScopeId>,

    members: UstrMap<ResourceId>,
    sub_scopes: UstrMap<ScopeId>,

    ghost_members: UstrMap<Vec<Dependency>>,
    ghost_scopes: UstrMap<Vec<Dependency>>,

    dependants: UstrMap<Vec<ResourceId>>,
}
