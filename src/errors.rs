use crate::location::Location;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ErrorId(usize);

pub struct ErrorCtx {
    errors: Vec<(Option<Location>, String)>,
    warnings: Vec<(Location, String)>,
}

impl Default for ErrorCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl ErrorCtx {
    pub const fn new() -> Self {
        Self {
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    pub fn join(&mut self, mut other: Self) {
        self.errors.append(&mut other.errors);
        self.warnings.append(&mut other.warnings);
    }

    pub fn print(&self) {
        for (loc, message) in &self.errors {
            print!("Error: ");
            println!("{:?}: {}", loc, message);
        }

        if self.errors.is_empty() {
            for (loc, message) in &self.warnings {
                print!("Warning: ");
                println!("{:?}: {}", loc, message);
            }
        }
    }

    pub fn global_error(&mut self, message: String) -> ErrorId {
        let id = ErrorId(self.errors.len());
        self.errors.push((None, message));
        id
    }

    pub fn error(&mut self, loc: Location, message: String) -> ErrorId {
        let id = ErrorId(self.errors.len());
        self.errors.push((Some(loc), message));
        id
    }

    pub fn warning(&mut self, loc: Location, message: String) {
        self.warnings.push((loc, message));
    }
}
