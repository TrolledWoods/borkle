use super::token_stream::TokenStream;
use crate::dependencies::DependencyList;
use crate::errors::ErrorCtx;
use crate::locals::{Label, LocalScopeId, LabelId, Local, LocalId, LocalVariables};
use crate::location::Location;
use crate::program::{Program, ScopeId};
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
    pub scope: ScopeId,
}

impl<'a> DataContext<'a> {
    pub fn new(
        errors: &'a mut ErrorCtx,
        program: &'a Program,
        tokens: &'a mut TokenStream,
        path: &'a Path,
        scope: ScopeId,
    ) -> Self {
        Self {
            errors,
            program,
            tokens,
            path,
            scope,
        }
    }

    pub fn error(&mut self, loc: Location, message: String) {
        self.errors.error(loc, message);
    }
}

pub struct ImperativeContext<'a> {
    pub locals: &'a mut LocalVariables,
    pub dependencies: &'a mut DependencyList,
    pub defer_depth: usize,
    pub evaluate_at_typing: bool,
    pub in_const_expression: bool,
    pub in_declarative_lvalue: bool,
    pub poly_args: &'a [(Location, Ustr)],
    default_labels: Vec<LabelId>,
    scope_boundaries: Vec<ScopeBoundary>,
    local_map: Vec<(Ustr, LocalScopeId)>,
}

impl<'a> ImperativeContext<'a> {
    pub fn new(
        dependencies: &'a mut DependencyList,
        locals: &'a mut LocalVariables,
        evaluate_at_typing: bool,
        poly_args: &'a [(Location, Ustr)],
    ) -> Self {
        Self {
            locals,
            dependencies,
            defer_depth: 0,
            evaluate_at_typing,
            in_const_expression: false,
            in_declarative_lvalue: false,
            poly_args,

            default_labels: Vec::new(),
            scope_boundaries: Vec::new(),
            local_map: Vec::new(),
        }
    }

    pub fn push_scope_boundary(&mut self) -> ScopeBoundaryId {
        let id = ScopeBoundaryId(self.scope_boundaries.len());
        self.scope_boundaries.push(ScopeBoundary {
            defer_depth: self.defer_depth,
            locals: self.local_map.len(),
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
    }

    pub fn insert_default_label(&mut self, name: Option<Ustr>, label: Label) -> LabelId {
        let id = self.locals.insert_label(label);
        self.default_labels.push(id);
        if let Some(name) = name {
            self.local_map.push((name, LocalScopeId::Label(id)));
        }
        id
    }

    pub fn last_default_label(&mut self) -> Option<LabelId> {
        self.default_labels.last().copied()
    }

    pub fn pop_default_label(&mut self) {
        self.default_labels.pop();
    }

    pub fn insert_label(&mut self, name: Ustr, label: Label) -> LabelId {
        let id = self.locals.insert_label(label);
        self.local_map.push((name, LocalScopeId::Label(id)));
        id
    }

    pub fn insert_local(&mut self, local: Local) -> LocalId {
        let name = local.name;
        let id = self.locals.insert(local);
        self.local_map.push((name, LocalScopeId::Local(id)));
        id
    }

    pub fn get_local(&self, name: Ustr) -> Option<LocalScopeId> {
        self.local_map
            .iter()
            .rev()
            .find_map(|&(local_name, id)| if local_name == name { Some(id) } else { None })
    }
}

struct ScopeBoundary {
    defer_depth: usize,
    locals: usize,
}
