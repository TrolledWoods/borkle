use super::token_stream::TokenStream;
use crate::dependencies::DependencyList;
use crate::errors::ErrorCtx;
use crate::locals::{Label, LocalScopeId, LabelId, Local, LocalId, LocalVariables, Polymorphic, PolymorphicId};
use crate::location::Location;
use crate::program::{Program, ScopeId};
use std::path::Path;
use ustr::Ustr;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeBoundaryId(usize);

/// A collection of various data that is needed for parsing
/// things in a data scope. Data scopes are scopes where constants
/// can be defined.
pub struct DataContext<'a, 'b> {
    pub errors: &'a mut ErrorCtx,
    pub program: &'a Program<'b>,
    pub tokens: &'a mut TokenStream,
    pub path: &'a Path,
    pub scope: ScopeId,
}

impl<'a, 'b> DataContext<'a, 'b> {
    pub fn new(
        errors: &'a mut ErrorCtx,
        program: &'a Program<'b>,
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

pub struct MappedLocal {
    pub name: Ustr,
    pub id: LocalScopeId,
    pub enabled: bool,
}

pub struct ImperativeContext<'a> {
    pub locals: &'a mut LocalVariables,
    pub dependencies: &'a mut DependencyList,
    pub defer_depth: usize,
    // TODO: These flags are too many, we want to just make a better version of this later
    // on that isn't garbage.
    pub evaluate_at_typing: bool,
    pub in_const_expression: bool,
    pub in_declarative_lvalue: bool,
    pub in_template_declaration: bool,
    // TODO: We should be able to get rid of this.
    pub poly_args: &'a [(Location, Ustr)],
    default_labels: Vec<LabelId>,
    scope_boundaries: Vec<ScopeBoundary>,
    local_map: Vec<MappedLocal>,
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
            in_template_declaration: false,
            poly_args,

            default_labels: Vec::new(),
            scope_boundaries: Vec::new(),
            local_map: Vec::new(),
        }
    }

    pub fn get_local_count(&self) -> usize {
        self.local_map.len()
    }

    pub fn whitelist_locals(&mut self, until: usize) {
        for local in &mut self.local_map[until..] {
            local.enabled = true;
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
            self.local_map.push(MappedLocal {
                name,
                id: LocalScopeId::Label(id),
                enabled: true,
            });
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
        self.local_map.push(MappedLocal {
            name,
            id: LocalScopeId::Label(id),
            enabled: true,
        });
        id
    }

    pub fn insert_local(&mut self, local: Local) -> LocalId {
        let name = local.name;
        let id = self.locals.insert(local);
        self.local_map.push(MappedLocal {
            name,
            id: LocalScopeId::Local(id),
            enabled: false,
        });
        id
    }

    pub fn insert_poly(&mut self, local: Polymorphic) -> PolymorphicId {
        let name = local.name;
        let id = self.locals.insert_poly(local);
        self.local_map.push(MappedLocal {
            name,
            id: LocalScopeId::Polymorphic(id),
            enabled: true,
        });
        id
    }

    pub fn get_local(&self, name: Ustr) -> Option<LocalScopeId> {
        self.local_map
            .iter()
            .rev()
            .filter(|v| v.enabled)
            .find_map(|mapped_local| if mapped_local.name == name { Some(mapped_local.id) } else { None })
    }
}

struct ScopeBoundary {
    defer_depth: usize,
    locals: usize,
}
