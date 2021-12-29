use crate::location::Location;
use crate::types::Type;
use ustr::Ustr;

#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
pub struct LocalId(pub usize);

#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
pub struct LabelId(pub usize);

#[derive(Debug, Clone)]
pub struct Local {
    pub name: Ustr,
    pub loc: Location,
    pub type_infer_value_id: crate::type_infer::ValueId,
    /// The "stack frame" that you're in. This is because you can mix inline constants and function declarations
    /// and stuff into the same scope, and we have to make sure that nobody tries to read the value of another
    /// set of things to execute. So when reading/writing to a value, you have to make sure that this id
    /// matches.
    pub stack_frame_id: crate::type_infer::ValueSetId,
    pub type_: Option<Type>,
    pub value: Option<crate::ir::Value>,
    pub uses: Vec<Location>,
    pub num_uses: usize,
}

impl Local {
    pub fn new(loc: Location, name: Ustr) -> Self {
        Self {
            name,
            loc,
            type_: None,
            type_infer_value_id: crate::type_infer::ValueId::NONE,
            stack_frame_id: 123123,
            value: None,
            uses: Vec::new(),
            num_uses: 0,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Label {
    pub loc: Location,
    /// This is how many many defers exist that aren't 'after' this label. defer_depth + num_defers
    /// is how many defers have to be inserted before jumping to the label, since num_defers
    /// are how many defers whose instructions can be combined with the target.
    pub defer_depth: usize,
    pub num_defers: usize,
    pub first_break_location: Option<Location>,
    pub type_infer_value_id: crate::type_infer::ValueId,
    pub stack_frame_id: crate::type_infer::ValueSetId,
    pub type_: Option<Type>,
    pub value: Option<crate::ir::Value>,
    pub ir_labels: Option<Vec<crate::ir::LabelId>>,
}

#[derive(Debug, Clone)]
pub struct LocalVariables {
    locals: Vec<Local>,
    labels: Vec<Label>,
}

impl LocalVariables {
    pub const fn new() -> Self {
        Self {
            locals: Vec::new(),
            labels: Vec::new(),
        }
    }

    pub fn insert(&mut self, local: Local) -> LocalId {
        let id = LocalId(self.locals.len());
        self.locals.push(local);
        id
    }

    pub fn insert_label(&mut self, label: Label) -> LabelId {
        let id = LabelId(self.labels.len());
        self.labels.push(label);
        id
    }

    #[allow(unused)]
    pub fn iter(&self) -> impl Iterator<Item = &'_ Local> {
        self.locals.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &'_ mut Local> {
        self.locals.iter_mut()
    }

    pub fn iter_labels_mut(&mut self) -> impl Iterator<Item = &'_ mut Label> {
        self.labels.iter_mut()
    }

    pub fn get_label(&self, id: LabelId) -> &Label {
        &self.labels[id.0]
    }

    pub fn get_label_mut(&mut self, id: LabelId) -> &mut Label {
        &mut self.labels[id.0]
    }

    pub fn get(&self, id: LocalId) -> &'_ Local {
        &self.locals[id.0]
    }

    pub fn get_mut(&mut self, id: LocalId) -> &'_ mut Local {
        &mut self.locals[id.0]
    }
}
