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
    pub fn with_one(&mut self, set_id: ValueSetId) -> ValueSetHandles {
        self.sets[set_id].uncomputed_values += 1;

        ValueSetHandles {
            sets: vec![set_id]
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
}

impl ValueSetHandles {
    pub fn is_empty(&self) -> bool {
        self.sets.is_empty()
    }

    // @Temporary thing for making it easier to migrate to the new system.
    // Intended for use with `combine_with`
    pub fn take(&mut self) -> Self {
        Self {
            sets: std::mem::take(&mut self.sets),
        }
    }

    pub fn make_erroneous(&mut self, value_sets: &mut ValueSets) {
        // We drain here(without decrementing counters),
        // because if the sets are erroneous they shouldn't get completed anyway.
        // @Correctness: Should we decrement the counters though? Maybe it's useful to see if all nodes
        // have finished emitting errors, though that doesn't quite work, with the way that errors propagate.
        for set in self.sets.drain(..) {
            value_sets.sets[set].has_errors = true;
        }
    }

    pub fn take_from(&mut self, mut other: ValueSetHandles, value_sets: &mut ValueSets) {
        for set in other.sets.drain(..) {
            if !self.insert_without_tracking(set) {
                // It already existed in self, so the number of total dependants is reduced.
                value_sets.sets[set].uncomputed_values -= 1;
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

    pub fn clone(&self, value_sets: &mut ValueSets) -> Self {
        let sets = self.sets.clone();
        for &set in &sets {
            value_sets.sets[set].uncomputed_values += 1;
        }
        Self {
            sets,
        }
    }

    // @Cleanup: It would be nice for complete to take ownership of self,
    // but I'm not going to do that for now.
    pub fn complete(&mut self, value_sets: &mut ValueSets) {
        for set in self.sets.drain(..) {
            value_sets.sets[set].uncomputed_values -= 1;
        }
    }

    pub fn contains(&self, id: ValueSetId) -> bool {
        self.sets.binary_search(&id).is_ok()
    }
}

impl Drop for ValueSetHandles {
    fn drop(&mut self) {
        if !self.sets.is_empty() {
            unreachable!("A value set cannot be dropped non-empty");
        }
    }
}
