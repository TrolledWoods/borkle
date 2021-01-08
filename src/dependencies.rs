use crate::location::Location;
use crate::program::{FunctionId, ScopeId};
use std::fmt;
use ustr::Ustr;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy)]
pub enum MemberDep {
    Type,
    Value,
    ValueAndCallableIfFunction,
}

#[derive(Clone)]
pub struct DependencyList {
    pub members: Vec<(ScopeId, Ustr, Location, MemberDep)>,
    pub calling: Vec<FunctionId>,
}

impl DependencyList {
    pub fn new() -> Self {
        Self {
            members: Vec::new(),
            calling: Vec::new(),
        }
    }

    pub fn add(&mut self, loc: Location, scope_id: ScopeId, name: Ustr, dep: MemberDep) {
        let entry = self
            .members
            .iter_mut()
            .find(|(s, n, _, _)| *s == scope_id && *n == name);

        if let Some((_, _, _, old_dep)) = entry {
            // If there was already an entry for this identifier, we want to look if the new
            // dependency is more general than the one before, and if it is, we want to replace the
            // old one with the new one.
            if *old_dep < dep {
                *old_dep = dep;
            }
        } else {
            self.members.push((scope_id, name, loc, dep));
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum DependencyKind {
    Type,
    Value,
    CallingNamed,
}

impl fmt::Debug for DependencyList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, " members: ")?;
        for (_, key, _, dep) in &self.members {
            write!(f, "{}: {:?}, ", key, dep)?;
        }
        write!(f, " calling: ")?;
        for calling in &self.calling {
            write!(f, "{:?}", calling)?;
        }
        Ok(())
    }
}
