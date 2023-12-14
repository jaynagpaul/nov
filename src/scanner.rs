use crate::parser::{Error, Result};
use crate::{Token, TokenKind};

pub struct Scanner {
    tokens: Vec<Token>,
    pos: usize,
}

impl Scanner {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, pos: 0 }
    }

    pub fn attempt<R>(&mut self, closure: impl Fn(&mut Scanner) -> Result<R>) -> Result<R> {
        let old_pos = self.pos;
        match closure(self) {
            Ok(r) => Ok(r),
            Err(e) => {
                self.pos = old_pos;
                Err(e)
            }
        }
    }

    pub fn attempt_all<R, F>(&mut self, closures: &[F]) -> Result<R>
    where
        F: Fn(&mut Scanner) -> Result<R>,
    {
        // let last_closure = closures.last().expect("Closures cannot be empty");
        // Iterate through everything but the last closure

        let all_but_last = closures.len() - 1;

        for closure in closures.iter().take(all_but_last) {
            match self.attempt(move |s| closure(s)) {
                Ok(r) => return Ok(r),
                Err(_) => continue,
            }
        }

        self.attempt(
            closures
                .last()
                .expect("attempt_all closures cannot be empty"),
        )
    }

    pub fn at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    /// Skips whitespace and newlines
    pub fn skip_newlines(&mut self) {
        while self.match_kind(&TokenKind::Newline).is_ok() {}
    }

    pub fn peek(&self) -> Result<&Token> {
        self.tokens.get(self.pos).ok_or(Error::UnexpectedEof)
    }

    pub fn advance(&mut self) -> Result<&Token> {
        if self.pos >= self.tokens.len() {
            Err(Error::UnexpectedEof)
        } else {
            self.pos += 1;
            Ok(&self.tokens[self.pos - 1])
        }
    }

    pub fn advance_if(&mut self, closure: impl FnOnce(&Token) -> Result<()>) -> Result<&Token> {
        {
            let token = self.peek()?;
            closure(token)?;
        };

        self.advance()
    }

    pub fn match_kind(&mut self, expected: &TokenKind) -> Result<&Token> {
        self.advance_if(|actual| {
            if actual.kind() == expected {
                Ok(())
            } else {
                Error::unexpected_token(actual.kind())
            }
        })
    }
}
