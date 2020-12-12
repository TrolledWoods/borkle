use super::token_stream::TokenStream;
use crate::dependencies::DependencyList;
use crate::errors::ErrorCtx;
use crate::locals::{Label, LabelId, Local, LocalId, LocalVariables};
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
    pub defer_depth: usize,
    pub evaluate_at_typing: bool,

    scope_boundaries: Vec<ScopeBoundary>,
    local_map: Vec<(Ustr, LocalId)>,
    label_map: Vec<(Ustr, LabelId)>,
}

impl<'a> ImperativeContext<'a> {
    pub fn new(dependencies: &'a mut DependencyList, evaluate_at_typing: bool) -> Self {
        Self {
            locals: LocalVariables::new(),
            dependencies,
            defer_depth: 0,
            evaluate_at_typing,

            scope_boundaries: Vec::new(),
            local_map: Vec::new(),
            label_map: Vec::new(),
        }
    }

    pub fn push_scope_boundary(&mut self) -> ScopeBoundaryId {
        let id = ScopeBoundaryId(self.scope_boundaries.len());
        self.scope_boundaries.push(ScopeBoundary {
            defer_depth: self.defer_depth,
            locals: self.local_map.len(),
            labels: self.label_map.len(),
        });
        id
    }

    pub fn pop_scope_boundary(&mut self) {
        let boundary = self
            .scope_boundaries
            .pop()
            .expect("called pop_scope_boundary without anything to pop");

        self.defer_depth = boundary.defer_depth;
        self.local_map.truncate(boundary.locals);
        self.label_map.truncate(boundary.labels);
    }

    pub fn insert_label(&mut self, label: Label) -> LabelId {
        let name = label.name;
        let id = self.locals.insert_label(label);
        self.label_map.push((name, id));
        id
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

    pub fn get_label(&self, name: Ustr) -> Option<LabelId> {
        self.label_map
            .iter()
            .rev()
            .find_map(|&(label_name, id)| if label_name == name { Some(id) } else { None })
    }
}

struct ScopeBoundary {
    defer_depth: usize,
    locals: usize,
    labels: usize,
}
