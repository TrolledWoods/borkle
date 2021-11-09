//!
//! Value sets are broken out into a separate module because they
//! are very particular to work with.
//!
//! It's very hard to manually manage the `uncomputed_values` correctly,
//! so this module is to force you(with the borrow checking rules), or at
//! least guide you, to correct code, so you never forget to increment
//! or decrement the values.
//!
//! This is also why `ValueSetHandles` doesn't implement `Clone`, since
//! cloning it requires you to increment the uncomputed values.
//!

pub type ValueSetId = usize;

#[derive(Default)]
pub struct ValueSets {
    sets: Vec<ValueSet>,
}

impl ValueSets {
    pub fn with_one(&mut self, set_id: ValueSetId, is_complete: bool) -> ValueSetHandles {
        if !is_complete {
            self.sets[set_id].uncomputed_values += 1;
        }

        ValueSetHandles {
            sets: vec![set_id],
            is_complete,
        }
    }

    pub fn add(&mut self, ast_node: crate::parser::ast::NodeId) -> ValueSetId {
        let id = self.sets.len();
        self.sets.push(ValueSet {
            uncomputed_values: 0,
            has_errors: false,
            related_nodes: Vec::new(),
            ast_node,
            has_been_computed: false,
        });
        id
    }

    pub fn add_node_to_set(&mut self, value_set: ValueSetId, node: crate::parser::ast::NodeId) {
        self.sets[value_set].related_nodes.push(node);
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
}

pub struct ValueSet {
    pub related_nodes: Vec<crate::parser::ast::NodeId>,

    uncomputed_values: i32,
    pub has_errors: bool,

    pub ast_node: crate::parser::ast::NodeId,
    pub has_been_computed: bool,
}

impl ValueSet {
    pub fn uncomputed_values(&self) -> i32 {
        self.uncomputed_values
    }
}

#[derive(Debug, Default)]
pub struct ValueSetHandles {
    sets: Vec<ValueSetId>,
    is_complete: bool,
}

impl ValueSetHandles {
    pub fn already_complete() -> Self {
        Self {
            sets: Vec::new(),
            is_complete: true,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.sets.is_empty()
    }

    /// Sets this set to another set. This is different from take_from, because
    /// it assumes that this set is _empty_, and not complete.
    pub fn set_to(&mut self, mut set: ValueSetHandles) {
        debug_assert!(!self.is_complete, "Called set_to on completed value");
        debug_assert!(self.sets.is_empty(), "Called set_to on non-empty value");
        self.sets = std::mem::take(&mut set.sets);
        self.is_complete = set.is_complete;
        set.is_complete = true;
    }

    // @Temporary thing for making it easier to migrate to the new system.
    // Intended for use with `combine_with`
    pub fn take(&mut self) -> Self {
        Self {
            sets: std::mem::take(&mut self.sets),
            is_complete: self.is_complete,
        }
    }

    pub fn make_erroneous(&mut self, value_sets: &mut ValueSets) {
        // We drain here(without decrementing counters),
        // because if the sets are erroneous they shouldn't get completed anyway.
        // @Correctness: Should we decrement the counters though? Maybe it's useful to see if all nodes
        // have finished emitting errors, though that doesn't quite work, with the way that errors propagate.
        for &set in &self.sets {
            value_sets.sets[set].has_errors = true;
        }

        self.is_complete = true;
    }

    pub fn take_from(&mut self, mut other: ValueSetHandles, value_sets: &mut ValueSets) {
        debug_assert!(!self.is_complete, "Cannot add more sets after completed");
        if !other.is_complete {
            for set in other.sets.drain(..) {
                if !self.insert_without_tracking(set) {
                    // It already existed in self, so the number of total dependants is reduced.
                    value_sets.sets[set].uncomputed_values -= 1;
                }
            }
        } else {
            for set in other.sets.drain(..) {
                if self.insert_without_tracking(set) {
                    // It didn't exist in self. Since the other set is complete, the values there aren't uncomputed.
                    value_sets.sets[set].uncomputed_values += 1;
                }
            }
        }
    }

    fn insert_without_tracking(&mut self, id: ValueSetId) -> bool {
        if let Err(index) = self.sets.binary_search(&id) {
            self.sets.insert(index, id);
            true
        } else {
            false
        }
    }

    pub fn clone(&self, value_sets: &mut ValueSets, already_complete: bool) -> Self {
        let sets = self.sets.clone();
        // We need all these already_complete flags, because make_erroneous needs to know all the
        // sets, so it can set all the ones that matter to erroneous.
        if !already_complete {
            for &set in &sets {
                value_sets.sets[set].uncomputed_values += 1;
            }
        }
        Self {
            sets,
            is_complete: already_complete,
        }
    }

    pub fn is_complete(&self) -> bool {
        self.is_complete
    }

    // @Cleanup: It would be nice for complete to take ownership of self,
    // but I'm not going to do that for now.
    pub fn complete(&mut self, value_sets: &mut ValueSets) {
        // Should this assert be here? Is it necessary
        // debug_assert!(!self.is_complete, "Cannot complete a set twice");
        if self.is_complete { return; }

        for &set in &self.sets {
            value_sets.sets[set].uncomputed_values -= 1;
        }

        self.is_complete = true;
    }

    pub fn contains(&self, id: ValueSetId) -> bool {
        self.sets.binary_search(&id).is_ok()
    }
}

// @Correctness: This crashes during incompleteness errors as well, because, they are incomplete. We should probably mass-flag all values as complete when generating incompleteness errors.
impl Drop for ValueSetHandles {
    fn drop(&mut self) {
        if !self.is_complete {
            unreachable!("A value set cannot be dropped non-completed");
        }
    }
}
