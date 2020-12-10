use crate::location::Location;
use crate::types::Type;
use ustr::Ustr;

#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
pub struct LocalId(usize);

#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
pub struct LabelId(usize);

#[derive(Debug, Clone)]
pub struct Local {
    pub name: Ustr,
    pub loc: Location,
    pub type_: Option<Type>,
    pub value: Option<crate::ir::Value>,
}

#[derive(Debug, Clone)]
pub struct Label {
    pub name: Ustr,
    pub loc: Location,
    pub type_: Option<Type>,
    pub value: Option<crate::ir::Value>,
    pub ir_label: Option<crate::ir::LabelId>,
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

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &'_ mut Local> {
        self.locals.iter_mut()
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
