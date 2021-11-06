use ustr::Ustr;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
    pub file: Ustr,
    pub line: u32,
    pub character: u32,
}

impl Location {
    pub const fn start(file: Ustr) -> Self {
        Self {
            file,
            line: 1,
            character: 1,
        }
    }

    pub fn next_char(&self) -> Self {
        Self {
            character: self.character + 1,
            ..*self
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
