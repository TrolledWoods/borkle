use ustr::Ustr;

#[derive(Debug, Clone)]
pub struct Token {
    pub loc: Location,
    pub kind: TokenKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    Keyword(Keyword),
    Identifier(Ustr),
    Literal(Literal),
    /// An operator can consist of several operators, it's just the rawest form
    /// of connected operator characters.
    Operator(Ustr),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    String(String),
    Int(u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Keyword {
    Const,
    If,
}

#[derive(Debug, Clone, Copy)]
pub struct Location {
    pub file: Ustr,
    pub line: usize,
    pub character: usize,
}

impl Location {
    const fn start(file: Ustr) -> Self {
        Self {
            file,
            line: 1,
            character: 1,
        }
    }
}

pub fn process_string(file: Ustr, string: &str) -> Vec<Token> {
    let mut tokens = Vec::new();

    // Create an iterator that iterates over the
    // code locations, byte indices and chars of the string.
    let mut chars = string
        .char_indices()
        .scan(Location::start(file), |loc, (index, character)| {
            let old_loc = *loc;
            match character {
                '\n' => {
                    loc.line += 1;
                    loc.character = 0;
                }
                '\t' => loc.character += 4,
                _ => loc.character += 1,
            }
            Some((old_loc, index, character))
        });

    let mut previous = None;
    while let Some((loc, index, character)) = previous.take().or_else(|| chars.next()) {
        match character {
            ' ' | '\t' | '\n' => (),
            '.' | ',' | '+' | '-' | '*' | '/' | '=' => {
                // Operator
                let start_index = index;
                let mut end_index = index;

                for (_, index, c) in &mut chars {
                    end_index = index;

                    if !matches!(c, '.' | ',' | '+' | '-' | '*' | '/' | '=') {
                        previous = Some((loc, index, c));
                        break;
                    }
                }

                tokens.push(Token {
                    loc,
                    kind: TokenKind::Operator(string[start_index..end_index].into()),
                });
            }
            c | c if c.is_alphabetic() || c == '_' => {
                // Identifier
                let start_index = index;
                let mut end_index = index;

                for (_, index, c) in &mut chars {
                    end_index = index;

                    if !(c.is_alphabetic() || c == '_' || c.is_digit(10)) {
                        previous = Some((loc, index, c));
                        break;
                    }
                }

                let identifier = &string[start_index..end_index];

                let kind = match identifier {
                    "const" => TokenKind::Keyword(Keyword::Const),
                    "if" => TokenKind::Keyword(Keyword::If),
                    _ => TokenKind::Identifier(identifier.into()),
                };

                tokens.push(Token { loc, kind });
            }
            c if c.is_digit(10) => {
                // Number
                let start_index = index;
                let mut end_index = index;

                for (_, index, c) in &mut chars {
                    end_index = index;

                    if !(c == '_' || c.is_digit(10)) {
                        previous = Some((loc, index, c));
                        break;
                    }
                }

                tokens.push(Token {
                    loc,
                    kind: TokenKind::Literal(Literal::Int(
                        string[start_index..end_index].parse().unwrap(),
                    )),
                });
            }
            _ => todo!("Error handling is not implemented yet"),
        }
    }

    tokens
}
