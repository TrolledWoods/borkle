use crate::location::Location;
use crate::program::{FunctionId, MemberId, ScopeId};
use std::cmp::Ordering;
use ustr::Ustr;

#[derive(Default, Clone, Debug)]
pub struct DependencyList {
    pub deps: Vec<(Location, DepKind)>,
}

impl DependencyList {
    pub fn new() -> Self {
        Self { deps: Vec::new() }
    }

    pub fn is_empty(&self) -> bool {
        self.deps.is_empty()
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

    /// This is an odd function, but essentially it's to allow for converting the dependencies for
    /// calculating the type of something to the dependencies needed for calculating the value of
    /// something. This is done by essentially saying that if you need the type of something, we
    /// will actually need the value of it because just needing the type is not enough.
    ///
    /// @Stability: Will this work for 'const'? Do we make all 'const's const at typing or
    /// something like that in this case?
    pub fn set_minimum_member_dep(&mut self, minimum: MemberDep) {
        for (_, dep) in &mut self.deps {
            match dep {
                DepKind::Member(_, dep) | DepKind::MemberByName(_, _, dep) => {
                    dep.combine_and_replace(minimum)
                }
                DepKind::Callable(_) => {}
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DepKind {
    /// This can also be used for polymorphic members, it doesn't matter, both use the same
    /// dependency in this case.
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
    fn combine_and_replace(&mut self, new: Self) {
        if let Combination::NewIsSuper = self.combine(new) {
            // If the new is a super dependency that means it includes both self and the new
            *self = new;
        }
    }

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
