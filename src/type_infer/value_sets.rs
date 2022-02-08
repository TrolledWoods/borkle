pub use super::AstVariantId;
pub type ValueSetId = usize;


#[derive(Clone, Default)]
pub struct ValueSets {
    sets: Vec<ValueSet>,
}

impl ValueSets {
    pub fn with_one(&mut self, set_id: ValueSetId) -> ValueSetHandles {
        self.sets[set_id].uncomputed_values += 1;
        unreachable!();

        ValueSetHandles {
            sets: Some(set_id),
            is_complete: false,
        }
    }

    pub fn add(&mut self, waiting_on_completion: crate::typer::WaitingOnTypeInferrence) -> ValueSetId {
        let id = self.sets.len();
        self.sets.push(ValueSet {
            uncomputed_values: 0,
            has_errors: false,
            related_nodes: Vec::new(),
            emit_deps: None,
            target_checker: None,
            waiting_on_completion,
            has_been_computed: false,
        });
        id
    }

    pub fn add_node_to_set(&mut self, value_set: ValueSetId, variant: AstVariantId, node: crate::ast::NodeId) {
        self.sets[value_set].related_nodes.push((variant, node));
    }


    pub fn iter_ids(&self) -> impl Iterator<Item = ValueSetId> {
        0..self.sets.len()
    }

    // Scary function!!! Should we have tracking for these too? They should
    // be used in very few places though...
    pub fn lock(&mut self, value_set: ValueSetId) {
        self.sets[value_set].uncomputed_values += 1;
    }

    // Scary function!!! Should we have tracking for these too? They should
    // be used in very few places though...
    pub fn unlock(&mut self, value_set: ValueSetId) {
        self.sets[value_set].uncomputed_values -= 1;
    }

    pub fn iter(&self) -> impl Iterator<Item = &'_ ValueSet> {
        self.sets.iter()
    }

    pub fn get(&self, set: ValueSetId) -> &ValueSet {
        &self.sets[set]
    }

    pub fn get_mut(&mut self, set: ValueSetId) -> &mut ValueSet {
        &mut self.sets[set]
    }

    pub fn make_erroneous(&mut self, set: &ValueSetHandles) {
        if let Some(set) = set.sets {
            self.sets[set].has_errors = true;
        }
    }

    pub fn is_erroneous(&self, set: &ValueSetHandles) -> bool {
        if let Some(set) = set.sets {
            if self.sets[set].has_errors {
                return true;
            }
        }

        false
    }
}

#[derive(Clone)]
pub struct ValueSet {
    pub related_nodes: Vec<(AstVariantId, crate::ast::NodeId)>,

    uncomputed_values: i32,
    pub has_errors: bool,

    // @Cleanup: I need to think about what a `ValueSet` is supposed to be, but the idea is that they
    // have to do with sub-sections of an Ast that can be emitted separately.
    pub waiting_on_completion: crate::typer::WaitingOnTypeInferrence,
    pub emit_deps: Option<crate::dependencies::DependencyList>,
    pub target_checker: Option<crate::typer::TargetChecker>,

    pub has_been_computed: bool,
}

impl ValueSet {
    pub fn uncomputed_values(&self) -> i32 {
        self.uncomputed_values
    }
}

#[derive(Clone, Debug)]
pub struct ValueSetHandles {
    sets: Option<ValueSetId>,
    is_complete: bool,
}

impl Default for ValueSetHandles {
    #[track_caller]
    fn default() -> Self {
        Self::empty()
    }
}

impl ValueSetHandles {
    pub fn empty() -> Self {
        Self {
            sets: None,
            is_complete: false,
        }
    }

    pub fn is_complete(&self) -> bool {
        self.is_complete
    }

    /// Sets this set to another set. This is different from take_from, because
    /// it assumes that this set is _empty_, and not complete.
    pub fn set_to(&mut self, mut set: ValueSetHandles) {
        debug_assert!(!self.is_complete, "Called set_to on completed value");
        debug_assert!(self.sets.is_none(), "Called set_to on non-empty value");
        self.sets = std::mem::take(&mut set.sets);
        self.is_complete = set.is_complete;
        set.is_complete = true;
    }

    pub fn take_from(&mut self, mut other: ValueSetHandles, value_sets: &mut ValueSets) {
        if let Some(set) = other.sets {
            if !other.is_complete {
                value_sets.sets[set].uncomputed_values -= 1;
            }

            if let Some(self_set) = self.sets {
                debug_assert_eq!(self_set, set, "take_from cannot cause more than one set to appear");
            } else {
                self.sets = Some(set);
                if !self.is_complete {
                    value_sets.sets[set].uncomputed_values += 1;
                }
            }
        }

        other.is_complete = true;
    }

    pub fn clone(&self, value_sets: &mut ValueSets) -> Self {
        let sets = self.sets;

        if let Some(set) = sets {
            value_sets.sets[set].uncomputed_values += 1;
        }

        Self {
            sets,
            is_complete: false,
        }
    }

    // @Cleanup: It would be nice for complete to take ownership of self,
    // but I'm not going to do that for now.
    pub fn complete(&mut self, value_sets: &mut ValueSets) {
        // Should this assert be here? Is it necessary
        // debug_assert!(!self.is_complete, "Cannot complete a set twice");
        if self.is_complete { return; }

        if let Some(set) = self.sets {
            value_sets.sets[set].uncomputed_values -= 1;
            debug_assert!(value_sets.sets[set].uncomputed_values >= 0);
        }

        self.is_complete = true;
    }
}
