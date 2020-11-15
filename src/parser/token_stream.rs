use super::lexer::{Token, TokenKind};
use crate::errors::ErrorCtx;
use crate::location::Location;
use crate::operators::{BinaryOp, UnaryOp};

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

    pub fn peek_mut(&mut self) -> Option<&'_ mut Token> {
        self.tokens.as_mut_slice().first_mut()
    }

    pub fn peek(&self) -> Option<&'_ Token> {
        self.tokens.as_slice().first()
    }

    pub fn expect_peek(&self, errors: &mut ErrorCtx) -> Result<&'_ Token, ()> {
        self.peek().ok_or_else(|| {
            errors.error(self.last, "Unexpected end of file".to_string());
        })
    }

    pub fn try_consume_access_operator(&mut self) -> Option<(Location, BinaryOp)> {
        let token = self.peek_mut()?;
        if let TokenKind::Operator(ref mut string) = token.kind {
            if let Some((op, suffix)) = BinaryOp::access_op_from_prefix(string) {
                let loc = token.loc;
                if suffix.is_empty() {
                    self.next();
                } else {
                    *string = suffix.into();
                }
                return Some((loc, op));
            }
        }
        None
    }

    pub fn try_consume_unary(&mut self) -> Option<(Location, UnaryOp)> {
        let token = self.peek_mut()?;
        if let TokenKind::Operator(ref mut string) = token.kind {
            if let Some((op, suffix)) = UnaryOp::from_prefix(string) {
                let loc = token.loc;
                if suffix.is_empty() {
                    self.next();
                } else {
                    *string = suffix.into();
                }
                return Some((loc, op));
            }
        }
        None
    }

    pub fn try_consume_binary(&mut self) -> Option<(Location, BinaryOp)> {
        let token = self.peek_mut()?;
        if let TokenKind::Operator(ref mut string) = token.kind {
            if let Some((op, suffix)) = BinaryOp::from_prefix(string) {
                let loc = token.loc;
                if suffix.is_empty() {
                    self.next();
                } else {
                    *string = suffix.into();
                }
                return Some((loc, op));
            }
        }
        None
    }

    pub fn try_consume_operator(&mut self, operator: &str) -> Option<()> {
        // This is complicated because multiple operators
        // could be mashed together into a single token.
        let token = self.peek_mut()?;
        if let TokenKind::Operator(ref mut string) = token.kind {
            // We can't use map here because closure
            // borrow checking SUCKS. Meh
            #[allow(clippy::option_if_let_else)]
            if let Some(rest) = string.strip_prefix(operator) {
                if rest.is_empty() {
                    self.next();
                } else {
                    *string = rest.into();
                }
                Some(())
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn try_consume(&mut self, errors: &mut ErrorCtx, kind: &TokenKind) -> Result<bool, ()> {
        if &self.expect_peek(errors)?.kind == kind {
            self.next();
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub fn expect_next_is(&mut self, errors: &mut ErrorCtx, kind: &TokenKind) -> Result<(), ()> {
        let token = self.expect_next(errors)?;
        if &token.kind == kind {
            Ok(())
        } else {
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
