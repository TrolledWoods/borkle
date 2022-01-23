use ustr::Ustr;
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Location {
    pub file: Ustr,
    pub line: u32,
    pub character: u32,
}

impl Location {
    pub fn unknown() -> Self {
        Self { file: "[unknown]".into(), line: 0, character: 0 }
    }

    pub const fn start(file: Ustr) -> Self {
        Self {
            file,
            line: 1,
            character: 1,
        }
    }

    pub fn increment_by_char(&mut self, character: char) {
        match character {
            '\n' => {
                self.line += 1;
                self.character = 1;
            }
            '\t' => self.character += 4,
            _ => self.character += 1,
        }
    }
}

impl fmt::Display for Location {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}:{},{}", self.file.as_str(), self.line, self.character)
    }
}
