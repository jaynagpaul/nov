use crate::{tokenize, Scanner, Token, TokenKind};

#[derive(Debug)]
pub enum Error {
    UnexpectedToken {
        expected: TokenKind,
        actual: TokenKind,
    },

    MissingExpr,

    UnexpectedEof,
}

impl Error {
    pub fn unexpected_token<R>(expected: &TokenKind, actual: &TokenKind) -> Result<R> {
        Err(Self::UnexpectedToken {
            expected: expected.clone(),
            actual: actual.clone(),
        })
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::UnexpectedToken { expected, actual } => {
                write!(f, "Expected token {:?}, got {:?}", expected, actual)
            }
            Error::UnexpectedEof => write!(f, "Unexpected EOF"),
            Error::MissingExpr => write!(f, "Missing expresssion"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

/// "\n"+
/// Decl+
/// Program
#[derive(Debug)]
pub struct Program {
    pub decls: Vec<Decl>,
}
fn program(s: &mut Scanner) -> Result<Program> {
    let mut decls = Vec::new();
    while !s.at_end() {
        s.skip_newlines();
        decls.push(decl(s)?);
        s.skip_newlines();
    }

    Ok(Program { decls })
}

/// FnDecl
#[derive(Debug)]
pub enum Decl {
    Fn(FnDecl),
}
fn decl(s: &mut Scanner) -> Result<Decl> {
    s.attempt(|s| fn_decl(s).map(Decl::Fn))
}

/// Fn Ident () Block
#[derive(Debug)]
pub struct FnDecl {
    pub name: String,

    pub block: Block,
}
fn fn_decl(s: &mut Scanner) -> Result<FnDecl> {
    use TokenKind::{Fn, Ident};

    s.match_kind(&Fn)?;

    let name = match s.advance()?.kind() {
        Ident(name) => name,
        actual => {
            return Err(Error::UnexpectedToken {
                expected: Ident("<Fn Name>".to_owned()),
                actual: actual.clone(),
            })
        }
    }
    .to_string();

    s.match_kind(&TokenKind::LParen)?;
    s.match_kind(&TokenKind::RParen)?;

    let block = block(s)?;

    Ok(FnDecl { name, block })
}

/// { Stmt+ }
#[derive(Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
}
fn block(s: &mut Scanner) -> Result<Block> {
    use TokenKind::{LBrace, RBrace};
    s.match_kind(&LBrace)?;

    let mut stmts = Vec::new();

    while s.match_kind(&RBrace).is_err() {
        s.skip_newlines();

        let stmt = stmt(s)?;
        stmts.push(stmt);

        s.skip_newlines();
    }

    Ok(Block { stmts })
}

/// fn_call_stmt | expr
#[derive(Debug)]
pub enum Stmt {
    FnCall(FnCallStmt),
    Expr(Expr),
}
fn stmt(s: &mut Scanner) -> Result<Stmt> {
    let fn_call_stmt = |s: &mut Scanner| Ok(Stmt::FnCall(fn_call_stmt(s)?));
    let expr_stmt = |s: &mut Scanner| Ok(Stmt::Expr(expr(s)?));

    let possible_stmts = [fn_call_stmt, expr_stmt];
    s.attempt_all(&possible_stmts)
}

/// Ident Expr+
#[derive(Debug)]
pub struct FnCallStmt {
    pub name: String,

    pub args: Vec<Expr>,
}
fn fn_call_stmt(s: &mut Scanner) -> Result<FnCallStmt> {
    let name = match s.advance()?.kind() {
        TokenKind::Ident(name) => name.to_string(),
        actual => {
            return Error::unexpected_token(&TokenKind::Ident("<Fn Name>".to_string()), actual)
        }
    };

    let args = exprs(s)?;

    Ok(FnCallStmt { name, args })
}

/// expr expr+
fn exprs(s: &mut Scanner) -> Result<Vec<Expr>> {
    let mut exprs = Vec::new();
    while let Ok(expr) = s.attempt(expr) {
        exprs.push(expr);
    }

    if exprs.is_empty() {
        Err(Error::MissingExpr)
    } else {
        Ok(exprs)
    }
}

/// (fn_call stmt) | StringLit | IntLit
#[derive(Debug)]
pub enum Expr {
    FnCall(FnCallStmt),
    StringLit(String),
    IntLit(i64),
}
fn expr(s: &mut Scanner) -> Result<Expr> {
    let expr_options = [paren_fn_call_stmt, string_lit, int_lit];

    s.attempt_all(&expr_options)
}

fn paren_fn_call_stmt(s: &mut Scanner) -> Result<Expr> {
    use TokenKind::{LParen, RParen};

    s.match_kind(&LParen)?;
    let call = fn_call_stmt(s)?;
    s.match_kind(&RParen)?;

    Ok(Expr::FnCall(call))
}

fn string_lit(s: &mut Scanner) -> Result<Expr> {
    match s.advance()?.kind() {
        TokenKind::StringLit(s) => Ok(Expr::StringLit(s.clone())),
        other => Error::unexpected_token(&TokenKind::StringLit("<string>".to_owned()), other),
    }
}

fn int_lit(s: &mut Scanner) -> Result<Expr> {
    match s.advance()?.kind() {
        TokenKind::IntLit(i) => Ok(Expr::IntLit(*i)),
        other => Error::unexpected_token(&TokenKind::IntLit(1234), other),
    }
}

#[test]
fn test_empty_function() {
    let content = r#"fn main() { }"#;

    let (tokens, _) = tokenize(content);

    let mut scanner = Scanner::new(tokens);

    let fn_decl = fn_decl(&mut scanner).unwrap();

    assert_eq!(fn_decl.name, "main")
}

#[cfg(test)]
mod tests {
    use expect_test::{expect, Expect};

    use super::*;

    fn parse(content: &str) -> Program {
        let (tokens, errs) = tokenize(content);
        assert_eq!(errs.len(), 0);

        let mut scanner = Scanner::new(tokens);
        program(&mut scanner).unwrap()
    }

    #[test]
    fn test_helloworld() {
        let content = r#"
    fn main() {
        print "hello world"
    }
"#;

        let program = parse(content);

        check(
            program,
            expect![[r#"
            Program {
                decls: [
                    Fn(
                        FnDecl {
                            name: "main",
                            block: Block {
                                stmts: [
                                    FnCall(
                                        FnCallStmt {
                                            name: "print",
                                            args: [
                                                StringLit(
                                                    "hello world",
                                                ),
                                            ],
                                        },
                                    ),
                                ],
                            },
                        },
                    ),
                ],
            }
        "#]],
        )
    }

    #[test]
    fn test_nested_func_calls() {
        let content = r#"fn main() {
            print "1 + 1 = " (plus "1" "1")
}"#;

        let program = parse(content);
        check(
            program,
            expect![[r#"
            Program {
                decls: [
                    Fn(
                        FnDecl {
                            name: "main",
                            block: Block {
                                stmts: [
                                    FnCall(
                                        FnCallStmt {
                                            name: "print",
                                            args: [
                                                StringLit(
                                                    "1 + 1 = ",
                                                ),
                                                FnCall(
                                                    FnCallStmt {
                                                        name: "plus",
                                                        args: [
                                                            StringLit(
                                                                "1",
                                                            ),
                                                            StringLit(
                                                                "1",
                                                            ),
                                                        ],
                                                    },
                                                ),
                                            ],
                                        },
                                    ),
                                ],
                            },
                        },
                    ),
                ],
            }
        "#]],
        );
    }

    fn check<T: std::fmt::Debug>(actual: T, expect: Expect) {
        expect.assert_debug_eq(&actual);
    }
}
