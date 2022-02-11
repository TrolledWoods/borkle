pub use super::AstVariantId;
pub type ValueSetId = usize;


#[derive(Clone, Default)]
pub struct ValueSets {
    sets: Vec<ValueSet>,
}

impl ValueSets {
    pub fn add(&mut self, waiting_on_completion: crate::typer::WaitingOnTypeInferrence) -> ValueSetId {
        let id = self.sets.len();
        self.sets.push(ValueSet {
            uncomputed_values: 0,
            has_errors: false,
            related_nodes: Vec::new(),
            ctx: None,
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
}

#[derive(Clone)]
pub struct ValueSet {
    pub related_nodes: Vec<(AstVariantId, crate::ast::NodeId)>,

    uncomputed_values: i32,
    pub has_errors: bool,

    // @Cleanup: I need to think about what a `ValueSet` is supposed to be, but the idea is that they
    // have to do with sub-sections of an Ast that can be emitted separately.
    pub waiting_on_completion: crate::typer::WaitingOnTypeInferrence,
    pub ctx: Option<crate::typer::AstVariantContext>,
    pub target_checker: Option<crate::typer::TargetChecker>,

    pub has_been_computed: bool,
}

impl ValueSet {
    pub fn uncomputed_values(&self) -> i32 {
        self.uncomputed_values
    }
}
