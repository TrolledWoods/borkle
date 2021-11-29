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
use std::panic::Location;

pub type ValueSetId = usize;

#[derive(Default)]
pub struct ValueSets {
    sets: Vec<ValueSet>,
}

impl ValueSets {
    #[track_caller]
    pub fn with_one(&mut self, set_id: ValueSetId, is_complete: bool) -> ValueSetHandles {
        if !is_complete {
            self.sets[set_id].uncomputed_values += 1;
        }

        ValueSetHandles {
            sets: Some(set_id),
            is_complete,
            caller_location: Location::caller(),
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

#[derive(Debug)]
pub struct ValueSetHandles {
    sets: Option<ValueSetId>,
    is_complete: bool,
    caller_location: &'static Location<'static>,
}

// @Cleanup: Remove this because it can be confusing....
impl Default for ValueSetHandles {
    #[track_caller]
    fn default() -> Self {
        Self::empty(false)
    }
}

impl ValueSetHandles {
    #[track_caller]
    pub fn empty(is_complete: bool) -> Self {
        Self {
            sets: None,
            is_complete,
            caller_location: Location::caller(),
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

    #[track_caller]
    pub fn clone(&self, value_sets: &mut ValueSets, already_complete: bool) -> Self {
        let sets = self.sets;
        // We need all these already_complete flags, because make_erroneous needs to know all the
        // sets, so it can set all the ones that matter to erroneous.
        if !already_complete {
            if let Some(set) = sets {
                value_sets.sets[set].uncomputed_values += 1;
            }
        }
        Self {
            sets,
            is_complete: already_complete,
            caller_location: Location::caller(),
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
        }

        self.is_complete = true;
    }
}

// @Correctness: This crashes during incompleteness errors as well, because, they are incomplete. We should probably mass-flag all values as complete when generating incompleteness errors.
impl Drop for ValueSetHandles {
    fn drop(&mut self) {
        if !self.is_complete && !std::thread::panicking() {
            unreachable!("A value set cannot be dropped non-completed, created at: {}", self.caller_location);
        }
    }
}
