use crate::location::Location;
use ustr::UstrMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ErrorId(usize);

type InfoList = Vec<(Location, String)>;

pub struct ErrorCtx {
    temp_info: Vec<(Location, String)>,
    errors: Vec<(Option<Location>, String, InfoList)>,
    warnings: Vec<(Location, String, InfoList)>,
}

impl Default for ErrorCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl ErrorCtx {
    pub const fn new() -> Self {
        Self {
            temp_info: Vec::new(),
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    pub fn join(&mut self, mut other: Self) {
        self.errors.append(&mut other.errors);
        self.warnings.append(&mut other.warnings);
    }

    pub fn print(&self, file_contents: &UstrMap<String>) -> bool {
        for &(loc, ref message, ref info) in &self.errors {
            println!("Error:");
            if let Some(loc) = loc {
                print_loc(loc, message, file_contents);
            } else {
                println!("{}", message);
            }

            for &(info_loc, ref info_message) in info {
                print_loc(info_loc, info_message, file_contents);
            }
        }

        if self.errors.is_empty() {
            for &(loc, ref message, ref info) in &self.warnings {
                println!("Warning: ");
                print_loc(loc, message, file_contents);

                for &(info_loc, ref info_message) in info {
                    print_loc(info_loc, info_message, file_contents);
                }
            }
        }

        self.errors.is_empty()
    }

    fn consume_info(&mut self) -> Vec<(Location, String)> {
        std::mem::replace(&mut self.temp_info, Vec::new())
    }

    pub fn info(&mut self, loc: Location, message: String) {
        self.temp_info.push((loc, message));
    }

    pub fn global_error(&mut self, message: String) {
        let info = self.consume_info();
        self.errors.push((None, message, info));
    }

    pub fn error(&mut self, loc: Location, message: String) {
        let info = self.consume_info();
        self.errors.push((Some(loc), message, info));
    }

    pub fn warning(&mut self, loc: Location, message: String) {
        let info = self.consume_info();
        self.warnings.push((loc, message, info));
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
