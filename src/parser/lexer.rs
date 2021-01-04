use super::token_stream::TokenStream;
use crate::errors::ErrorCtx;
use crate::literal::Literal;
use crate::location::Location;
use crate::types::{IntTypeKind, Type, TypeKind};
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
    SingleQuote,
    Tag(Ustr),
    Open(Bracket),
    Close(Bracket),
    Keyword(Keyword),
    Identifier(Ustr),
    Literal(Literal),
    /// An operator token can consist of several operators, it's just the rawest form
    /// of connected operator characters.
    Operator(Ustr),

    Type(Type),
    PrimitiveInt(IntTypeKind),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bracket {
    Round,
    Curly,
    Square,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Keyword {
    Intrinsic,
    Entry,
    Any,
    Break,
    Type,
    Const,
    In,
    Let,
    Defer,
    If,
    For,
    While,
    Else,
    Function,
    BitCast,
    Uninit,
    Zeroed,
    Bool,
    Import,
    Library,
}

pub fn process_string(errors: &mut ErrorCtx, file: Ustr, string: &str) -> Result<TokenStream, ()> {
    let mut tokens = Vec::new();

    // Create an iterator that iterates over the
    // code locations, byte indices and chars of the string.
    let mut loc = Location::start(file);
    let mut chars = string
        .char_indices()
        .map(|(index, character)| {
            let old_loc = loc;
            loc.increment_by_char(character);
            (old_loc, index, character)
        })
        .peekable();

    while let Some(&(loc, _, character)) = chars.peek() {
        let kind = match character {
            c if c.is_whitespace() => {
                chars.next();
                continue;
            }

            ';' | '\'' | ',' | '(' | ')' | '[' | ']' | '{' | '}' => {
                chars.next();
                match character {
                    '\'' => TokenKind::SingleQuote,
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

            '#' => {
                chars.next();
                let tag_name = slice_while(
                    string,
                    &mut chars,
                    |c| matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9'),
                );

                match tag_name {
                    "entry" => TokenKind::Keyword(Keyword::Entry),
                    "uninit" => TokenKind::Keyword(Keyword::Uninit),
                    "0" => TokenKind::Keyword(Keyword::Zeroed),
                    "import_intrinsic_from_compiler" => TokenKind::Keyword(Keyword::Intrinsic),
                    _ => TokenKind::Tag(tag_name.into()),
                }
            }

            'a'..='z' | 'A'..='Z' | '_' => {
                let identifier = slice_while(
                    string,
                    &mut chars,
                    |c| matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9'),
                );

                match identifier {
                    "const" => TokenKind::Keyword(Keyword::Const),
                    "type" => TokenKind::Keyword(Keyword::Type),
                    "break" => TokenKind::Keyword(Keyword::Break),
                    "any" => TokenKind::Keyword(Keyword::Any),
                    "let" => TokenKind::Keyword(Keyword::Let),
                    "defer" => TokenKind::Keyword(Keyword::Defer),
                    "fn" => TokenKind::Keyword(Keyword::Function),
                    "if" => TokenKind::Keyword(Keyword::If),
                    "else" => TokenKind::Keyword(Keyword::Else),
                    "bit_cast" => TokenKind::Keyword(Keyword::BitCast),
                    "bool" => TokenKind::Keyword(Keyword::Bool),
                    "while" => TokenKind::Keyword(Keyword::While),
                    "for" => TokenKind::Keyword(Keyword::For),
                    "in" => TokenKind::Keyword(Keyword::In),
                    "import" => TokenKind::Keyword(Keyword::Import),
                    "library" => TokenKind::Keyword(Keyword::Library),

                    "f32" => TokenKind::Type(Type::new(TypeKind::F32)),
                    "f64" => TokenKind::Type(Type::new(TypeKind::F64)),

                    "isize" => TokenKind::PrimitiveInt(IntTypeKind::Isize),
                    "usize" => TokenKind::PrimitiveInt(IntTypeKind::Usize),
                    "i64" => TokenKind::PrimitiveInt(IntTypeKind::I64),
                    "u64" => TokenKind::PrimitiveInt(IntTypeKind::U64),
                    "i32" => TokenKind::PrimitiveInt(IntTypeKind::I32),
                    "u32" => TokenKind::PrimitiveInt(IntTypeKind::U32),
                    "i16" => TokenKind::PrimitiveInt(IntTypeKind::I16),
                    "u16" => TokenKind::PrimitiveInt(IntTypeKind::U16),
                    "i8" => TokenKind::PrimitiveInt(IntTypeKind::I8),
                    "u8" => TokenKind::PrimitiveInt(IntTypeKind::U8),
                    _ => TokenKind::Identifier(identifier.into()),
                }
            }
            '0'..='9' => lex_number(errors, loc, &mut chars)?,
            '"' => TokenKind::Literal(Literal::String(string_literal(errors, &mut chars)?)),

            c if is_operator_token(c) => {
                let string = slice_while(string, &mut chars, is_operator_token);

                // FIXME: Is this the best place to put comment checking?
                // It's certainly versatile, but maybe we want a separate place
                // for them?
                if string.starts_with("//") {
                    for (_, _, c) in &mut chars {
                        if c == '\n' {
                            break;
                        }
                    }

                    continue;
                }

                TokenKind::Operator(string.into())
            }
            c => {
                errors.error(loc, format!("Unknown character {:?}", c));
                return Err(());
            }
        };

        tokens.push(Token { loc, kind });
    }

    Ok(TokenStream::new(loc, tokens))
}

fn lex_number(
    errors: &mut ErrorCtx,
    loc: Location,
    chars: &mut Peekable<impl Iterator<Item = (Location, usize, char)>>,
) -> Result<TokenKind, ()> {
    fn lex_basic_number(
        chars: &mut Peekable<impl Iterator<Item = (Location, usize, char)>>,
        base: u32,
        digit_count: &mut i32,
    ) -> u64 {
        let mut number = 0;

        while let Some(&(_, _, c)) = chars.peek() {
            if let Some(digit) = c.to_digit(base) {
                chars.next();
                number *= u64::from(base);
                number += u64::from(digit);
                *digit_count += 1;
            } else if c == '_' {
                chars.next();
            } else {
                break;
            }
        }

        number
    }

    let first = lex_basic_number(chars, 10, &mut 0);

    if let Some(&(_, _, c)) = chars.peek() {
        match c {
            'x' => {
                chars.next();

                if first != 0 {
                    errors.error(
                        loc,
                        "Expected '0' before 'x' in hexadecimal integer literal".to_string(),
                    );
                    return Err(());
                }

                Ok(TokenKind::Literal(Literal::Int(i128::from(
                    lex_basic_number(chars, 16, &mut 0),
                ))))
            }
            'b' => {
                chars.next();

                // Use the first as a base for the second number
                if first > 36 {
                    errors.error(loc, "Too large base, max is 36".to_string());
                    return Err(());
                }

                #[allow(clippy::cast_possible_truncation)]
                Ok(TokenKind::Literal(Literal::Int(i128::from(
                    lex_basic_number(chars, first as u32, &mut 0),
                ))))
            }
            '.' => {
                let mut digits = 0;
                let fractal_part = lex_basic_number(chars, 10, &mut digits);

                #[allow(clippy::cast_precision_loss)]
                let float = first as f64 + (fractal_part as f64 / 10.0_f64.powi(digits));
                Ok(TokenKind::Literal(Literal::Float(float)))
            }
            _ => Ok(TokenKind::Literal(Literal::Int(i128::from(first)))),
        }
    } else {
        Ok(TokenKind::Literal(Literal::Int(i128::from(first))))
    }
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
) -> Result<String, ()> {
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
                Some((_, _, '0')) => string.push('\0'),
                Some((loc, _, c)) => {
                    errors.error(
                        loc,
                        format!("\\{:?} is not a character escape character", c),
                    );
                    return Err(());
                }
                None => {
                    errors.error(loc, "String literal was not closed".to_string());
                    return Err(());
                }
            },

            Some((_, _, c)) => string.push(c),

            None => {
                errors.error(loc, "String literal was not closed".to_string());
                return Err(());
            }
        }
    }

    Ok(string)
}

const fn is_operator_token(c: char) -> bool {
    matches!(
        c,
        '+' | '-' | '*' | '/' | '&' | '!' | '=' | ':' | '<' | '>' | '.' | '|'
    )
}
