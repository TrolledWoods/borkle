use super::token_stream::TokenStream;
use crate::dependencies::DependencyList;
use crate::errors::ErrorCtx;
use crate::locals::{Local, LocalId, LocalVariables};
use crate::location::Location;
use crate::program::Program;
use std::path::Path;
use ustr::Ustr;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeBoundaryId(usize);

/// A collection of various data that is needed for parsing
/// things in a data scope. Data scopes are scopes where constants
/// can be defined.
pub struct DataContext<'a> {
    pub errors: &'a mut ErrorCtx,
    pub program: &'a Program,
    pub tokens: &'a mut TokenStream,
    pub path: &'a Path,
}

impl<'a> DataContext<'a> {
    pub fn new(
        errors: &'a mut ErrorCtx,
        program: &'a Program,
        tokens: &'a mut TokenStream,
        path: &'a Path,
    ) -> Self {
        Self {
            errors,
            program,
            tokens,
            path,
        }
    }

    pub fn error(&mut self, loc: Location, message: String) {
        self.errors.error(loc, message);
    }
}

pub struct ImperativeContext<'a> {
    pub locals: LocalVariables,
    pub dependencies: &'a mut DependencyList,

    scope_boundaries: Vec<ScopeBoundary>,
    local_map: Vec<(Ustr, LocalId)>,
}

impl<'a> ImperativeContext<'a> {
    pub fn new(dependencies: &'a mut DependencyList) -> Self {
        Self {
            locals: LocalVariables::new(),
            dependencies,

            scope_boundaries: Vec::new(),
            local_map: Vec::new(),
        }
    }

    pub fn push_scope_boundary(&mut self) -> ScopeBoundaryId {
        let id = ScopeBoundaryId(self.scope_boundaries.len());
        self.scope_boundaries.push(ScopeBoundary {
            locals: self.local_map.len(),
        });
        id
    }

    pub fn pop_scope_boundary(&mut self) {
        let boundary = self
            .scope_boundaries
            .pop()
            .expect("called pop_scope_boundary without anything to pop");

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
            .find_map(|&(local_name, id)| if local_name == name { Some(id) } else { None })
    }
}

struct ScopeBoundary {
    locals: usize,
}
