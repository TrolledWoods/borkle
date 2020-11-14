use crate::errors::{ErrorCtx, ErrorId};
use crate::location::Location;
use core::iter::Peekable;
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
    /// An operator token can consist of several operators, it's just the rawest form
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
            loc.increment_by_char(character);
            Some((old_loc, index, character))
        })
        .peekable();

    while let Some(&(loc, _, character)) = chars.peek() {
        let kind = match character {
            ' ' | '\t' | '\n' => {
                chars.next();
                continue;
            }

            ';' | ',' | '(' | ')' | '[' | ']' | '{' | '}' => {
                chars.next();
                match character {
                    ';' => TokenKind::SemiColon,
                    ',' => TokenKind::Comma,

                    '(' => TokenKind::Open(Bracket::Round),
                    ')' => TokenKind::Close(Bracket::Round),

                    '[' => TokenKind::Open(Bracket::Square),
                    ']' => TokenKind::Close(Bracket::Square),

                    '{' => TokenKind::Open(Bracket::Curly),
                    '}' => TokenKind::Close(Bracket::Curly),
                    _ => unreachable!(),
                }
            }

            '.' | '+' | '-' | '*' | '/' | '=' => {
                let string = slice_while(string, &mut chars, |c| {
                    matches!(c, '.' | '+' | '-' | '*' | '/' | '=')
                });

                TokenKind::Operator(string.into())
            }
            'a'..='z' | 'A'..='Z' | '_' => {
                let identifier = slice_while(
                    string,
                    &mut chars,
                    |c| matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9'),
                );

                match identifier {
                    "const" => TokenKind::Keyword(Keyword::Const),
                    "if" => TokenKind::Keyword(Keyword::If),
                    "let" => TokenKind::Keyword(Keyword::Let),
                    _ => TokenKind::Identifier(identifier.into()),
                }
            }
            '0'..='9' => {
                let string = slice_while(string, &mut chars, |c| c.is_digit(10) || c == '_');

                TokenKind::Literal(Literal::Int(string.parse().unwrap()))
            }
            '"' => TokenKind::Literal(Literal::String(string_literal(errors, &mut chars)?)),
            c => return Err(errors.error(loc, format!("Unknown character {:?}", c))),
        };

        tokens.push(Token { loc, kind });
    }

    tokens.shrink_to_fit();
    Ok(tokens)
}

/// Creates a string slice while a predicate is true.
/// The immediately next element is always included.
fn slice_while<'a>(
    string: &'a str,
    chars: &mut Peekable<impl Iterator<Item = (Location, usize, char)>>,
    mut predicate: impl FnMut(char) -> bool,
) -> &'a str {
    let (_, start_index, _) = chars.next().unwrap();

    while let Some(&(_, index, character)) = chars.peek() {
        if !predicate(character) {
            return &string[start_index..index];
        }

        chars.next();
    }

    &string[start_index..]
}

fn string_literal(
    errors: &mut ErrorCtx,
    chars: &mut impl Iterator<Item = (Location, usize, char)>,
) -> Result<String, ErrorId> {
    let mut string = String::new();

    let (loc, _, first_char) = chars.next().unwrap();
    debug_assert_eq!(first_char, '"');

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
                None => return Err(errors.error(loc, "String literal was not closed".to_string())),
            },

            Some((_, _, c)) => string.push(c),

            None => return Err(errors.error(loc, "String literal was not closed".to_string())),
        }
    }

    Ok(string)
}
