pub fn tokenize(content: &str) -> (Vec<Token>, Vec<Error>) {
    Tokenizer::tokenize(content.to_string())
}

#[derive(Debug, Copy, Clone)]
pub struct Loc {
    pos: usize,
    line: usize,
}

#[derive(Debug)]
pub struct Token {
    kind: TokenKind,

    loc: Loc,
}

#[derive(PartialEq, Debug, Clone)]
pub enum TokenKind {
    // Brackets
    LParen,
    RParen,
    LBrace,
    RBrace,
    Newline,

    // Arithmetic
    Plus,
    Minus,
    Star,
    Slash,

    // Literals
    StringLit(String),
    IntLit(i64),
    Ident(String),

    // Keywords
    Fn,
}

struct Tokenizer {
    input: Vec<char>,
    loc: Loc,
}

pub struct Error {
    kind: ErrorKind,
    loc: Loc,
}

#[derive(Debug)]
pub enum ErrorKind {
    ExpectedEof,
    UnexpectedEof,
}

#[derive(PartialEq)]
enum State {
    Start,

    // To compress multiple newlines into one
    Newline,

    Ident(String),
    StringLit(String),
    IntLit(String),
}

impl Tokenizer {
    fn new(input: String) -> Self {
        Self {
            input: input.chars().collect(),
            loc: Loc { pos: 0, line: 0 },
        }
    }

    fn tokenize(content: String) -> (Vec<Token>, Vec<Error>) {
        let mut tokens = Vec::new();
        let mut errors = Vec::new();

        let mut tokenizer = Tokenizer::new(content);

        loop {
            let token = match tokenizer.next_token() {
                Ok(token) => token,
                Err(e) if matches!(e.kind, ErrorKind::ExpectedEof) => break,
                Err(err) => {
                    errors.push(err);
                    continue;
                }
            };

            tokens.push(token);
        }

        (tokens, errors)
    }

    fn next_token(&mut self) -> Result<Token, Error> {
        use ErrorKind::*;
        use TokenKind::*;

        // Helper method to reduce boilerplate
        let mut state = State::Start;

        loop {
            let c = match self.advance() {
                Some(c) => c,
                None => {
                    return match state {
                        State::Start => self.error(ExpectedEof),
                        State::StringLit(_) => return self.error(UnexpectedEof),
                        State::Newline => self.token(Newline),
                        State::Ident(ident) => self.token(Ident(ident)),
                        State::IntLit(str) => self.token(IntLit(str.parse().unwrap())),
                    }
                }
            };

            match state {
                State::Start => match c {
                    '(' => return self.token(LParen),
                    ')' => return self.token(RParen),
                    '{' => return self.token(LBrace),
                    '}' => return self.token(RBrace),
                    '+' => return self.token(Plus),
                    '-' => return self.token(Minus),
                    '*' => return self.token(Star),
                    '/' => return self.token(Slash),

                    '\n' => state = State::Newline,

                    c if Self::is_whitespace(c) => continue,

                    c if c.is_alphabetic() => state = State::Ident(c.to_string()),
                    c if c.is_numeric() => state = State::IntLit(c.to_string()),

                    '"' => state = State::StringLit(String::new()),

                    c => panic!("Unexpected char {:?}", c),
                },

                // To compress multiple newlines into one
                State::Newline => match c {
                    '\n' => continue,
                    _ => {
                        self.backtrack();
                        return self.token(Newline);
                    }
                },

                State::Ident(mut ident) => match c {
                    c if c.is_alphanumeric() => {
                        ident.push(c);
                        state = State::Ident(ident);
                    }

                    _ => {
                        self.backtrack();

                        match ident.as_str() {
                            "fn" => return self.token(Fn),
                            _ => return self.token(Ident(ident)),
                        }
                    }
                },

                State::StringLit(mut lit) => match c {
                    '"' => return self.token(StringLit(lit)),
                    _ => {
                        lit.push(c);
                        state = State::StringLit(lit);
                    }
                },

                State::IntLit(mut lit) => match c {
                    _ if c.is_numeric() => {
                        lit.push(c);
                        state = State::IntLit(lit);
                    }

                    _ => {
                        self.backtrack();
                        return self.token(IntLit(lit.parse().unwrap()));
                    }
                },
            }
        }
    }

    fn is_whitespace(c: char) -> bool {
        c == ' ' || c == '\t'
    }

    fn error(&self, kind: ErrorKind) -> Result<Token, Error> {
        Err(Error {
            kind,
            loc: self.loc,
        })
    }

    fn token(&self, kind: TokenKind) -> Result<Token, Error> {
        Ok(Token::new(kind, self.loc))
    }

    fn at_end(&self) -> bool {
        self.loc.pos >= self.input.len()
    }

    fn backtrack(&mut self) {
        self.loc.pos -= 1;
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.input.get(self.loc.pos).cloned();

        match c {
            Some(c) => {
                if c == '\n' {
                    self.loc.line += 1;
                }
                self.loc.pos += 1;

                Some(c)
            }
            None => return None,
        }
    }
}

impl Token {
    pub fn new(kind: TokenKind, loc: Loc) -> Self {
        Self { kind, loc }
    }

    pub fn kind(&self) -> &TokenKind {
        &self.kind
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_tokenkinds(tokens: &[Token], expected: &[TokenKind]) {
        assert_eq!(tokens.len(), expected.len());

        for (token, expected) in tokens.iter().zip(expected.iter()) {
            assert_eq!(token.kind(), expected);
        }
    }

    #[test]
    fn test_helloworld() {
        use TokenKind::*;

        let tokens = tokenize(
            r#"fn main() {
    print "Hello, world!"
}"#,
        );

        let expected_tokens = vec![
            Fn,
            Ident("main".to_string()),
            LParen,
            RParen,
            LBrace,
            Newline,
            Ident("print".to_string()),
            StringLit("Hello, world!".to_string()),
            Newline,
            RBrace,
        ];

        check_tokenkinds(&tokens.0, &expected_tokens);
    }
}
