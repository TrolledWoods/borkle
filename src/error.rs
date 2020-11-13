use crate::location::Location;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ErrorId(usize);

pub struct ErrorCtx {
    errors: Vec<(Location, String)>,
    warnings: Vec<(Location, String)>,
}

impl Default for ErrorCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl ErrorCtx {
    pub fn new() -> Self {
        Self {
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    pub fn error(&mut self, loc: Location, message: String) -> ErrorId {
        let id = ErrorId(self.errors.len());
        self.errors.push((loc, message));
        id
    }

    pub fn warning(&mut self, loc: Location, message: String) {
        self.warnings.push((loc, message));
    }
}
