use super::token_stream::TokenStream;
use crate::errors::ErrorCtx;
use crate::location::Location;
use crate::types::{IntTypeKind, Type};
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
    IntLiteral(i128),
    CharLiteral(u8),
    StringLiteral(String),
    CStringLiteral(Vec<u8>),
    ArrayStringLiteral(Vec<u8>),
    FloatLiteral(f64),
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
    Int,
    Float,
    Underscore,
    Entry,
    Void,
    Any,
    All,
    Break,
    Type,
    Const,
    Enum,
    In,
    Is,
    Let,
    Defer,
    If,
    For,
    While,
    Else,
    Function,
    Explain,
    Cast,
    BitCast,
    Uninit,
    Zeroed,
    Bool,
    Import,
    Library,
    BuiltinFunction,
    TypeOf,
    SizeOf,
    Extern,
    Pack,
    Unpack,
}

pub fn process_string(errors: &mut ErrorCtx, file: Ustr, string: &str) -> Result<(TokenStream, u64), ()> {
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

    while let Some(&(loc, index, character)) = chars.peek() {
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
                    "builtin_function" => TokenKind::Keyword(Keyword::BuiltinFunction),
                    _ => TokenKind::Tag(tag_name.into()),
                }
            }

            'c' if string[index+1..].chars().next() == Some('"') => {
                chars.next();
                let mut literal = string_literal(errors, &mut chars)?.into_bytes();
                // Push the terminating character.
                literal.push(0);
                TokenKind::CStringLiteral(literal)
            },
            'a' if string[index+1..].chars().next() == Some('"') => {
                chars.next();
                TokenKind::ArrayStringLiteral(string_literal(errors, &mut chars)?.into_bytes())
            },
            's' if string[index+1..].chars().next() == Some('"') => {
                chars.next();
                // TODO: This is not very fast...
                let string = string_literal(errors, &mut chars)?;
                if string.len() != 1 {
                    errors.error(loc, "Char literals have to contain exactly one character".to_string());
                    return Err(());
                }

                if string.as_bytes()[0] >= 128 {
                    errors.error(loc, "Char literals can only contain ascii characters for now".to_string());
                    return Err(());
                }

                TokenKind::CharLiteral(string.as_bytes()[0])
            },

            'a'..='z' | 'A'..='Z' | '_' => {
                let identifier = slice_while(
                    string,
                    &mut chars,
                    |c| matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9'),
                );

                match identifier {
                    "explain" => TokenKind::Keyword(Keyword::Explain),
                    "const" => TokenKind::Keyword(Keyword::Const),
                    "enum" => TokenKind::Keyword(Keyword::Enum),
                    "type" => TokenKind::Keyword(Keyword::Type),
                    "break" => TokenKind::Keyword(Keyword::Break),
                    "any" => TokenKind::Keyword(Keyword::Any),
                    "all" => TokenKind::Keyword(Keyword::All),
                    "void" => TokenKind::Keyword(Keyword::Void),
                    "let" => TokenKind::Keyword(Keyword::Let),
                    "defer" => TokenKind::Keyword(Keyword::Defer),
                    "fn" => TokenKind::Keyword(Keyword::Function),
                    "if" => TokenKind::Keyword(Keyword::If),
                    "else" => TokenKind::Keyword(Keyword::Else),
                    "cast" => TokenKind::Keyword(Keyword::Cast),
                    "bit_cast" => TokenKind::Keyword(Keyword::BitCast),
                    "bool" => TokenKind::Keyword(Keyword::Bool),
                    "while" => TokenKind::Keyword(Keyword::While),
                    "for" => TokenKind::Keyword(Keyword::For),
                    "in" => TokenKind::Keyword(Keyword::In),
                    "is" => TokenKind::Keyword(Keyword::Is),
                    "typeof" => TokenKind::Keyword(Keyword::TypeOf),
                    "sizeof" => TokenKind::Keyword(Keyword::SizeOf),
                    "import" => TokenKind::Keyword(Keyword::Import),
                    "library" => TokenKind::Keyword(Keyword::Library),
                    "extern" => TokenKind::Keyword(Keyword::Extern),
                    "pack" => TokenKind::Keyword(Keyword::Pack),
                    "unpack" => TokenKind::Keyword(Keyword::Unpack),
                    "_" => TokenKind::Keyword(Keyword::Underscore),

                    "f32" => TokenKind::Type(Type::new_float(4)),
                    "f64" => TokenKind::Type(Type::new_float(8)),

                    "Int" => TokenKind::Keyword(Keyword::Int),
                    "Float" => TokenKind::Keyword(Keyword::Float),
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
            '"' => TokenKind::StringLiteral(string_literal(errors, &mut chars)?),

            c if is_operator_token(c) => {
                // FIXME: Is this the best place to put comment checking?
                // It's certainly versatile, but maybe we want a separate place
                // for them?
                if string[index..].starts_with("/*") {
                    chars.next();

                    let mut blocks = Vec::new();

                    let mut building_new = true;
                    let mut num_stars = 0;
                    let mut finished = false;
                    let mut building_loc = loc;
                    for (location, _, c) in &mut chars {
                        if c == '*' {
                            num_stars += 1;
                        } else {
                            if c == '/' {
                                if num_stars > 0 {
                                    if building_new {
                                        // This is a case like /****/, which we just ignore. May still be the out-most block though, so we have to check for completion
                                        building_new = false;
                                        if blocks.is_empty() {
                                            finished = true;
                                            break;
                                        }
                                    } else {
                                        // A closing thing, like this: '***/'
                                        let &(opened_pos, last) = blocks.last().unwrap();

                                        if last < num_stars {
                                            errors.info(opened_pos, format!("Opened here"));
                                            errors.error(location, format!("Tried closing a block comment with {} stars, but the opening only had {}\n(you can use more stars on the outer block comment to ignore the inner, like this: `/*** /*  ***/`)", num_stars, last));
                                        };

                                        if last == num_stars {
                                            blocks.pop();

                                            if blocks.is_empty() {
                                                finished = true;
                                                break;
                                            }
                                        }
                                    }
                                } else {
                                    // There are no stars in front, so we can just set building new as true
                                    building_new = true;
                                    building_loc = location;
                                }
                            } else if building_new {
                                if num_stars > 0 {
                                    blocks.push((building_loc, num_stars));
                                }

                                building_new = false;
                            }
                            
                            num_stars = 0;
                        }
                    }

                    if !finished {
                        errors.error(loc, format!("Unclosed block comment"));
                        return Err(());
                    }

                    continue;
                } else if string[index..].starts_with("//") {
                    for (_, _, c) in &mut chars {
                        if c == '\n' {
                            break;
                        }
                    }

                    continue;
                }

                let string = slice_while(string, &mut chars, is_operator_token);
                TokenKind::Operator(string.into())
            }
            c => {
                errors.error(loc, format!("Unknown character {:?}", c));
                return Err(());
            }
        };

        tokens.push(Token { loc, kind });
    }

    Ok((TokenStream::new(loc, tokens), loc.line as u64))
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

                Ok(TokenKind::IntLiteral(i128::from(
                    lex_basic_number(chars, 16, &mut 0),
                )))
            }
            'b' => {
                chars.next();

                // Use the first as a base for the second number
                if first > 36 {
                    errors.error(loc, "Too large base, max is 36".to_string());
                    return Err(());
                }

                #[allow(clippy::cast_possible_truncation)]
                Ok(TokenKind::IntLiteral(i128::from(
                    lex_basic_number(chars, first as u32, &mut 0),
                )))
            }
            '.' => {
                chars.next();

                let mut digits = 0;
                let fractal_part = lex_basic_number(chars, 10, &mut digits);

                #[allow(clippy::cast_precision_loss)]
                let float = first as f64 + (fractal_part as f64 / 10.0_f64.powi(digits));
                Ok(TokenKind::FloatLiteral(float))
            }
            _ => Ok(TokenKind::IntLiteral(i128::from(first))),
        }
    } else {
        Ok(TokenKind::IntLiteral(i128::from(first)))
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
                Some((_, _, 's')) => while !matches!(chars.next(), Some((_, _, '\\')) | None) {},
                Some((_, _, '"')) => string.push('"'),
                Some((_, _, '\\')) => string.push('\\'),
                Some((_, _, 'n')) => string.push('\n'),
                Some((_, _, 't')) => string.push('\t'),
                Some((_, _, '0')) => string.push('\0'),
                Some((_, _, 'r')) => string.push('\r'),
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
        '+' | '-' | '*' | '/' | '&' | '!' | '=' | ':' | '<' | '>' | '.' | '|' | '%'
    )
}
