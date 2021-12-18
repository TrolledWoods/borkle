use crate::location::Location;
use ustr::{Ustr, UstrMap};

const ANSI_RED:     &str = "\x1b[31m";
const ANSI_YELLOW:  &str = "\x1b[33m";
// const ANSI_WHITE:   &str = "\x1b[37m";
const ANSI_DEFAULT: &str = "\x1b[39m";
const ANSI_DIM: &str = "\x1b[2m";
const ANSI_RESET_DIM: &str = "\x1b[22m";

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ErrorId(usize);

type InfoList = Vec<(Location, String)>;

#[derive(Default)]
pub struct ErrorCtx {
    temp_info: Vec<(Location, String)>,
    errors: Vec<(Option<Location>, String, InfoList)>,
    warnings: Vec<(Location, String, InfoList)>,
    notes: Vec<(Location, String, InfoList)>,
}

impl ErrorCtx {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn join(&mut self, mut other: Self) {
        self.errors.append(&mut other.errors);
        self.warnings.append(&mut other.warnings);
        self.notes.append(&mut other.notes);
    }

    pub fn clear(&mut self) {
        self.temp_info.clear();
        self.errors.clear();
        self.warnings.clear();
        self.notes.clear();
    }

    pub fn print(&self, file_contents: &UstrMap<String>) -> bool {
        for &(loc, ref message, ref info) in &self.notes {
            let mut prev_file = None;
            println!("NOTE: ");
            print_loc(&mut prev_file, loc, message, file_contents);

            for &(info_loc, ref info_message) in info {
                print_loc(&mut prev_file, info_loc, info_message, file_contents);
            }

            println!();
        }

        for &(loc, ref message, ref info) in &self.errors {
            let mut prev_file = None;
            print!("{}ERROR: {}", ANSI_RED, ANSI_DEFAULT);
            if let Some(loc) = loc {
                print_loc(&mut prev_file, loc, message, file_contents);
            } else {
                println!("{}", message);
            }

            for &(info_loc, ref info_message) in info {
                print_loc(&mut prev_file, info_loc, info_message, file_contents);
            }

            println!();
        }

        if self.errors.is_empty() {
            for &(loc, ref message, ref info) in &self.warnings {
                let mut prev_file = None;
                println!("{}WARNING: {}", ANSI_YELLOW, ANSI_DEFAULT);
                print_loc(&mut prev_file, loc, message, file_contents);

                for &(info_loc, ref info_message) in info {
                    print_loc(&mut prev_file, info_loc, info_message, file_contents);
                }
            }

            println!();
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

    pub fn note(&mut self, loc: Location, message: String) {
        let info = self.consume_info();
        self.notes.push((loc, message, info));
    }
}

fn print_loc(prev_file: &mut Option<Ustr>, loc: Location, message: &str, file_contents: &UstrMap<String>) {
    // Hacky method of getting the relative path from a canonalized path.
    let current_dir = std::fs::canonicalize(".\\").map_or_else(|_| String::new(), |p| p.to_string_lossy().into_owned() + "\\");
    let file = loc.file.strip_prefix(&current_dir).unwrap_or(&loc.file);

    if let Some(content) = file_contents.get(&loc.file) {
        if let Some(line) = content.lines().nth(loc.line as usize - 1) {
            let prefix = format!("{:>4} | ", loc.line);

            // Only print the file name if we're in a new file
            if prev_file.as_ref().map_or(true, |v| *v != loc.file) {
                println!("{}in {}:{}", ANSI_DIM, file, ANSI_RESET_DIM);
            } else {
                println!();
            }

            println!("{}{}{}{}", ANSI_DIM, prefix, ANSI_RESET_DIM, line);

            print!("{}", " ".repeat(prefix.len()));
            for c in line.chars().take(loc.character as usize - 1) {
                if c.is_whitespace() {
                    print!("{}", c);
                } else {
                    print!(" ");
                }
            }
            if prefix.len() + message.len() <= 80 {
                println!("{}^{} {}", ANSI_RED, ANSI_DEFAULT, message);
            } else {
                println!("{}^{}", ANSI_RED, ANSI_DEFAULT);
                println!("{}{}", " ".repeat(prefix.len() - 2), message);
            }
        } else {
            println!("{} {}: {}", file, loc.line, message);
        }
    } else {
        println!("{} {}: {}", file, loc.line, message);
    }

    *prev_file = Some(loc.file);
}
