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
    Const,
    Let,
    Defer,
    Extern,
    If,
    While,
    Else,
    Function,
    BitCast,
    Uninit,
    Bool,
    Import,
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
        // We allow this so that operator character matching
        // can use ranges and be somewhat concise.
        // This means however that the operator branch
        // must be at the bottom.
        #[allow(overlapping_patterns)]
        let kind =
            match character {
                c if c.is_whitespace() => {
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

                'a'..='z' | 'A'..='Z' | '_' => {
                    let identifier = slice_while(
                        string,
                        &mut chars,
                        |c| matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9'),
                    );

                    match identifier {
                        "const" => TokenKind::Keyword(Keyword::Const),
                        "let" => TokenKind::Keyword(Keyword::Let),
                        "defer" => TokenKind::Keyword(Keyword::Defer),
                        "fn" => TokenKind::Keyword(Keyword::Function),
                        "if" => TokenKind::Keyword(Keyword::If),
                        "else" => TokenKind::Keyword(Keyword::Else),
                        "extern" => TokenKind::Keyword(Keyword::Extern),
                        "bit_cast" => TokenKind::Keyword(Keyword::BitCast),
                        "uninit" => TokenKind::Keyword(Keyword::Uninit),
                        "bool" => TokenKind::Keyword(Keyword::Bool),
                        "while" => TokenKind::Keyword(Keyword::While),
                        "import" => TokenKind::Keyword(Keyword::Import),

                        "f32" => TokenKind::Type(Type::new(TypeKind::F32)),
                        "f64" => TokenKind::Type(Type::new(TypeKind::F64)),

                        "i8" => TokenKind::PrimitiveInt(IntTypeKind::I8),
                        "u8" => TokenKind::PrimitiveInt(IntTypeKind::U8),

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
                '0'..='9' => {
                    let string = slice_while(string, &mut chars, |c| c.is_digit(10) || c == '.');

                    if string.contains('.') {
                        TokenKind::Literal(Literal::Float(string.parse().expect(
                            "Error message for float literal parsing fails are not done yet",
                        )))
                    } else {
                        TokenKind::Literal(Literal::Int(string.parse().unwrap()))
                    }
                }
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
        '+' | '-' | '*' | '/' | '&' | '!' | '=' | ':' | '<' | '>' | '.'
    )
}
