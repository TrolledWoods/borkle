use crate::location::Location;
use crate::types::Type;
use ustr::Ustr;

#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
pub struct LocalId(usize);

#[derive(Debug)]
pub struct Local {
    pub name: Ustr,
    pub loc: Location,
    pub type_: Option<Type>,
}

#[derive(Debug)]
pub struct LocalVariables {
    locals: Vec<Local>,
}

impl LocalVariables {
    pub const fn new() -> Self {
        Self { locals: Vec::new() }
    }

    pub fn insert(&mut self, local: Local) -> LocalId {
        let id = LocalId(self.locals.len());
        self.locals.push(local);
        id
    }

    #[allow(unused)]
    pub fn get(&self, id: LocalId) -> &'_ Local {
        &self.locals[id.0]
    }

    #[allow(unused)]
    pub fn get_mut(&mut self, id: LocalId) -> &'_ mut Local {
        &mut self.locals[id.0]
    }
}
