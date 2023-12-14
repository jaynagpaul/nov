mod decl;
mod expr;
mod scanner;
mod stmt;

use crate::{parser::decl::fn_decl, tokenize, TokenKind};

use self::{
    decl::{decl, Decl},
    expr::{atom_exprs, expr, Expr},
    scanner::Scanner,
};

#[derive(Debug)]
pub enum Error {
    UnexpectedToken { actual: TokenKind },

    MissingExpr,

    UnexpectedEof,
}

impl Error {
    pub fn unexpected_token<R>(actual: &TokenKind) -> Result<R> {
        Err(Self::UnexpectedToken {
            actual: actual.clone(),
        })
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::UnexpectedToken { actual } => {
                write!(f, "Expected different token, got {:?}", actual)
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
    fn test_arithmetic() {
        let content = r#"1 + 2 * 4 - 3 "#;

        let (tokens, _) = tokenize(content);

        let mut scanner = Scanner::new(tokens);

        let expr = expr(&mut scanner);

        check(
            expr,
            expect![[r#"
                Ok(
                    BinaryOp(
                        BinOpExpr {
                            left: BinaryOp(
                                BinOpExpr {
                                    left: IntLit(
                                        1,
                                    ),
                                    op: Plus,
                                    right: BinaryOp(
                                        BinOpExpr {
                                            left: IntLit(
                                                2,
                                            ),
                                            op: Star,
                                            right: IntLit(
                                                4,
                                            ),
                                        },
                                    ),
                                },
                            ),
                            op: Minus,
                            right: IntLit(
                                3,
                            ),
                        },
                    ),
                )
            "#]],
        )
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
