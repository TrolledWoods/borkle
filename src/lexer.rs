use crate::errors::{ErrorCtx, ErrorId};
use crate::location::Location;
use ustr::Ustr;

#[derive(Debug, Clone)]
pub struct Token {
    pub loc: Location,
    pub kind: TokenKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    SemiColon,
    Comma,
    Open(Bracket),
    Close(Bracket),
    Keyword(Keyword),
    Identifier(Ustr),
    Literal(Literal),
    /// An operator can consist of several operators, it's just the rawest form
    /// of connected operator characters.
    Operator(Ustr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bracket {
    Round,
    Curly,
    Square,
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
    Let,
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

pub fn process_string(
    errors: &mut ErrorCtx,
    file: Ustr,
    string: &str,
) -> Result<Vec<Token>, ErrorId> {
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
        let kind = match character {
            ' ' | '\t' | '\n' => continue,

            ';' => TokenKind::SemiColon,
            ',' => TokenKind::Comma,

            '(' => TokenKind::Open(Bracket::Round),
            ')' => TokenKind::Close(Bracket::Round),

            '[' => TokenKind::Open(Bracket::Square),
            ']' => TokenKind::Close(Bracket::Square),

            '{' => TokenKind::Open(Bracket::Curly),
            '}' => TokenKind::Close(Bracket::Curly),

            '.' | '+' | '-' | '*' | '/' | '=' => {
                // Operator
                let start_index = index;
                let mut end_index = index;

                for (_, index, c) in &mut chars {
                    end_index = index;

                    if !matches!(c, '.' | '+' | '-' | '*' | '/' | '=') {
                        previous = Some((loc, index, c));
                        break;
                    }
                }

                TokenKind::Operator(string[start_index..end_index].into())
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

                match identifier {
                    "const" => TokenKind::Keyword(Keyword::Const),
                    "if" => TokenKind::Keyword(Keyword::If),
                    "let" => TokenKind::Keyword(Keyword::Let),
                    _ => TokenKind::Identifier(identifier.into()),
                }
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

                TokenKind::Literal(Literal::Int(
                    string[start_index..end_index].parse().unwrap(),
                ))
            }
            '"' => {
                let mut string = String::new();

                loop {
                    match chars.next() {
                        Some((_, _, '"')) => break,
                        Some((_, _, '\\')) => match chars.next() {
                            Some((_, _, '"')) => string.push('"'),
                            Some((_, _, '\\')) => string.push('\\'),

                            Some((_, _, 'n')) => string.push('\n'),
                            Some((_, _, 't')) => string.push('\t'),

                            Some((loc, _, c)) => {
                                return Err(errors.error(
                                    loc,
                                    format!("\\{:?} is not a character escape character", c),
                                ))
                            }
                            None => {
                                return Err(
                                    errors.error(loc, "String literal was not closed".to_string())
                                )
                            }
                        },
                        Some((_, _, c)) => string.push(c),
                        None => {
                            return Err(
                                errors.error(loc, "String literal was not closed".to_string())
                            )
                        }
                    }
                }

                TokenKind::Literal(Literal::String(string))
            }
            c => return Err(errors.error(loc, format!("Unknown character {:?}", c))),
        };

        tokens.push(Token { loc, kind });
    }

    tokens.shrink_to_fit();
    Ok(tokens)
}
