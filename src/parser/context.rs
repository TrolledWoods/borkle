use super::token_stream::TokenStream;
use super::Ast;
use crate::errors::ErrorCtx;
use crate::locals::{Local, LocalId, LocalVariables};
use crate::location::Location;
use ustr::Ustr;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeBoundaryId(usize);

pub struct GlobalContext<'a> {
    pub errors: &'a mut ErrorCtx,
    pub tokens: &'a mut TokenStream,
}

impl<'a> GlobalContext<'a> {
    pub fn new(errors: &'a mut ErrorCtx, tokens: &'a mut TokenStream) -> Self {
        Self { errors, tokens }
    }

    pub fn error(&mut self, loc: Location, message: String) {
        self.errors.error(loc, message);
    }

    pub fn local(&mut self) -> Context<'_> {
        Context {
            errors: self.errors,
            tokens: self.tokens,
            locals: LocalVariables::new(),

            scope_boundaries: Vec::new(),
            defers: Vec::new(),
            local_map: Vec::new(),
        }
    }
}

pub struct Context<'a> {
    pub locals: LocalVariables,
    pub errors: &'a mut ErrorCtx,
    pub tokens: &'a mut TokenStream,

    scope_boundaries: Vec<ScopeBoundary>,
    defers: Vec<Ast>,
    local_map: Vec<(Ustr, LocalId)>,
}

impl<'a> Context<'a> {
    pub fn global(&mut self) -> GlobalContext<'_> {
        GlobalContext {
            errors: self.errors,
            tokens: self.tokens,
        }
    }

    pub fn error(&mut self, loc: Location, message: String) {
        self.errors.error(loc, message);
    }

    pub fn push_scope_boundary(&mut self) -> ScopeBoundaryId {
        let id = ScopeBoundaryId(self.scope_boundaries.len());
        self.scope_boundaries.push(ScopeBoundary {
            defers: self.defers.len(),
            locals: self.local_map.len(),
        });
        id
    }

    pub fn pop_scope_boundary(&mut self) {
        let boundary = self
            .scope_boundaries
            .pop()
            .expect("called pop_scope_boundary without anything to pop");

        self.defers.truncate(boundary.defers);
        self.local_map.truncate(boundary.locals);
    }

    pub fn insert_local(&mut self, local: Local) -> LocalId {
        let name = local.name;
        let id = self.locals.insert(local);
        self.local_map.push((name, id));
        id
    }

    pub fn get_local(&self, name: Ustr) -> Option<LocalId> {
        self.local_map
            .iter()
            .rev()
            .find_map(|&(local_name, id)| (local_name == name).then_some(id))
    }

    pub fn push_defer(&mut self, defer: Ast) {
        self.defers.push(defer);
    }

    pub fn defers_to(&self, index: ScopeBoundaryId) -> impl Iterator<Item = &Ast> {
        self.defers[self.scope_boundaries[index.0].defers..]
            .iter()
            .rev()
    }
}

struct ScopeBoundary {
    defers: usize,
    locals: usize,
}
