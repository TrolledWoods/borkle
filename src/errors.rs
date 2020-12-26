use crate::location::Location;
use ustr::UstrMap;

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

    pub fn print(&self, file_contents: &UstrMap<String>) {
        for &(loc, ref message) in &self.errors {
            println!("Error:");
            if let Some(loc) = loc {
                print_loc(loc, message, file_contents);
            } else {
                println!("{}", message);
            }
        }

        if self.errors.is_empty() {
            for &(loc, ref message) in &self.warnings {
                println!("Warning: ");
                print_loc(loc, message, file_contents);
            }
        }
    }

    pub fn global_error(&mut self, message: String) {
        self.errors.push((None, message));
    }

    pub fn error(&mut self, loc: Location, message: String) {
        self.errors.push((Some(loc), message));
    }

    pub fn warning(&mut self, loc: Location, message: String) {
        self.warnings.push((loc, message));
    }
}

fn print_loc(loc: Location, message: &str, file_contents: &UstrMap<String>) {
    if let Some(content) = file_contents.get(&loc.file) {
        if let Some(line) = content.lines().nth(loc.line as usize - 1) {
            let prefix = format!("{:>4} | ", loc.line);

            println!("{}{}", prefix, line);

            print!("{}", " ".repeat(prefix.len()));
            for c in line.chars().take(loc.character as usize - 1) {
                if c.is_whitespace() {
                    print!("{}", c);
                } else {
                    print!(" ");
                }
            }
            println!("^");
            println!("{}{}", " ".repeat(prefix.len() - 2), message);
        } else {
            println!("{} {}: {}", loc.file, loc.line, message);
        }
    } else {
        println!("{} {}: {}", loc.file, loc.line, message);
    }
}
