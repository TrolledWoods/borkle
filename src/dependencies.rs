use crate::location::Location;
use crate::program::{FunctionId, MemberId, ScopeId};
use std::cmp::Ordering;
use ustr::Ustr;

#[derive(Clone, Debug)]
pub struct DependencyList {
    pub deps: Vec<(Location, DepKind)>,
}

impl DependencyList {
    pub fn new() -> Self {
        Self { deps: Vec::new() }
    }

    pub fn add(&mut self, loc: Location, new: DepKind) {
        for (_, old) in &mut self.deps {
            match old.combine(new) {
                Combination::None => {}
                Combination::NewIsSuper => {
                    *old = new;
                    return;
                }
                Combination::Identical | Combination::OldIsSuper => return,
            }
        }

        self.deps.push((loc, new));
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DepKind {
    MemberByName(ScopeId, Ustr, MemberDep),
    Member(MemberId, MemberDep),
    Callable(FunctionId),
}

impl DepKind {
    fn combine(self, new: Self) -> Combination {
        match (self, new) {
            (
                DepKind::MemberByName(old_scope, old_name, old_dep),
                DepKind::MemberByName(new_scope, new_name, new_dep),
            ) if old_scope == new_scope && old_name == new_name => old_dep.combine(new_dep),
            (DepKind::Member(old_id, old_dep), DepKind::Member(new_id, new_dep))
                if old_id == new_id =>
            {
                old_dep.combine(new_dep)
            }
            (DepKind::Callable(old_id), DepKind::Callable(new_id)) if old_id == new_id => {
                Combination::Identical
            }
            _ => Combination::None,
        }
    }
}

#[derive(PartialOrd, Ord, PartialEq, Eq, Debug, Clone, Copy)]
pub enum MemberDep {
    Type,
    Value,
    ValueAndCallableIfFunction,
}

impl MemberDep {
    fn combine(self, new: Self) -> Combination {
        match self.cmp(&new) {
            Ordering::Less => Combination::NewIsSuper,
            Ordering::Greater => Combination::OldIsSuper,
            Ordering::Equal => Combination::Identical,
        }
    }
}

enum Combination {
    /// They can't be combined
    None,
    /// The current one is a superset of the new one
    OldIsSuper,
    /// The new one is a superset of the old one
    NewIsSuper,
    /// They are the same
    Identical,
}
