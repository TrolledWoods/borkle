use super::lexer::{Token, TokenKind, Keyword};
use crate::errors::ErrorCtx;
use crate::location::Location;
use crate::operators::{BinaryOp, Operator, UnaryOp};
use ustr::Ustr;

pub struct TokenStream {
    last: Location,
    tokens: std::vec::IntoIter<Token>,
}

impl TokenStream {
    pub fn new(last: Location, tokens: Vec<Token>) -> Self {
        Self {
            last,
            tokens: tokens.into_iter(),
        }
    }

    pub fn loc(&self) -> Location {
        self.peek().map_or(self.last, |token| token.loc)
    }

    pub fn peek_mut(&mut self) -> Option<&'_ mut Token> {
        self.tokens.as_mut_slice().first_mut()
    }

    pub fn peek(&self) -> Option<&'_ Token> {
        self.tokens.as_slice().first()
    }

    pub fn peek_nth(&self, index: usize) -> Option<&'_ Token> {
        self.tokens.as_slice().get(index)
    }

    pub fn expect_identifier(&mut self, errors: &mut ErrorCtx) -> Result<(Location, Ustr), ()> {
        match self.next() {
            Some(Token {
                loc,
                kind: TokenKind::Identifier(name),
            }) => Ok((loc, name)),
            Some(Token { loc, .. }) => {
                errors.error(loc, "Expected identifier".to_string());
                Err(())
            }
            None => {
                errors.error(self.last, "Expected identifier".to_string());
                Err(())
            }
        }
    }

    #[allow(unused)]
    pub fn expect_peek(&self, errors: &mut ErrorCtx) -> Result<&'_ Token, ()> {
        self.peek().ok_or_else(|| {
            errors.error(self.last, "Unexpected end of file".to_string());
        })
    }

    pub fn try_consume_operator_with_precedence(
        &mut self,
        precedence: usize,
    ) -> Option<(Location, BinaryOp)> {
        let token = self.peek_mut()?;
        match token.kind {
            TokenKind::Operator(ref mut string) => {
                if let Some((op, suffix)) = BinaryOp::from_prefix(string) {
                    if op.is_right_to_left() {
                        if op.precedence() < precedence {
                            return None;
                        }
                    } else {
                        if op.precedence() <= precedence {
                            return None;
                        }
                    }

                    let loc = token.loc;
                    if suffix.is_empty() {
                        self.next();
                    } else {
                        *string = suffix.into();
                    }
                    Some((loc, op))
                } else {
                    None
                }
            }
            TokenKind::Keyword(Keyword::Is) => {
                let loc = token.loc;
                self.next();

                Some((loc, BinaryOp::Is))
            }
            _ => None,
        }
    }

    pub fn try_consume_operator_with_metadata<T: Operator>(
        &mut self,
    ) -> Option<(Location, T, OperatorConsumptionMeta)> {
        let token = self.peek_mut()?;
        if let TokenKind::Operator(ref mut string) = token.kind {
            if let Some((op, suffix)) = T::from_prefix(string) {
                let loc = token.loc;
                let mut cleared_operator_string = false;
                if suffix.is_empty() {
                    cleared_operator_string = true;
                    self.next();
                } else {
                    *string = suffix.into();
                }
                return Some((
                    loc,
                    op,
                    OperatorConsumptionMeta {
                        cleared_operator_string,
                    },
                ));
            }
        }
        None
    }

    pub fn try_consume_operator<T: Operator>(&mut self) -> Option<(Location, T)> {
        self.try_consume_operator_with_metadata()
            .map(|(loc, val, _)| (loc, val))
    }

    pub fn try_consume_operator_string(&mut self, prefix: &str) -> Option<Location> {
        let token = self.peek_mut()?;
        if let TokenKind::Operator(ref mut string) = token.kind {
            if let Some(suffix) = string.strip_prefix(prefix) {
                let loc = token.loc;
                if suffix.is_empty() {
                    self.next();
                } else {
                    *string = suffix.into();
                }
                return Some(loc);
            }
        }
        None
    }

    pub fn try_consume_with_data(&mut self, wanted: &TokenKind) -> Option<Location> {
        if matches!(self.peek(), Some(Token { kind, .. }) if kind == wanted) {
            Some(self.next().unwrap().loc)
        } else {
            None
        }
    }

    pub fn try_consume(&mut self, wanted: &TokenKind) -> bool {
        self.try_consume_with_data(wanted).is_some()
    }

    pub fn expect_next_is(&mut self, errors: &mut ErrorCtx, kind: &TokenKind) -> Result<(), ()> {
        let token = self.expect_next(errors)?;
        if &token.kind == kind {
            Ok(())
        } else {
            if self.try_consume_operator::<UnaryOp>().is_some() {
                errors.error(token.loc, "Unary operator is not allowed here".to_string());
                return Err(());
            }

            errors.error(token.loc, format!("Expected '{:?}'", kind));
            Err(())
        }
    }

    pub fn expect_next(&mut self, errors: &mut ErrorCtx) -> Result<Token, ()> {
        self.next().ok_or_else(|| {
            errors.error(self.last, "Unexpected end of file".to_string());
        })
    }
}

impl Iterator for TokenStream {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.tokens.next()
    }
}

pub struct OperatorConsumptionMeta {
    pub cleared_operator_string: bool,
}
