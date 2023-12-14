use crate::{tokenize, Scanner, Token, TokenKind};

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
        actual => return Error::unexpected_token(actual),
    };

    let args = atom_exprs(s)?;

    Ok(FnCallStmt { name, args })
}

/// atom_expr atom_expr+
fn atom_exprs(s: &mut Scanner) -> Result<Vec<Expr>> {
    let mut exprs = Vec::new();
    while let Ok(expr) = s.attempt(atom_expr) {
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
    BinaryOp(BinOpExpr),
    FnCall(FnCallStmt),
    StringLit(String),
    IntLit(i64),
}

fn expr(s: &mut Scanner) -> Result<Expr> {
    expr_bp(s, 0)
}

/// Takes in the minimum binding power, stops evaluating when the left binding power is less than the minimum
fn expr_bp(s: &mut Scanner, min_bp: u8) -> Result<Expr> {
    let mut lhs = atom_expr(s)?;

    loop {
        let op = match s.peek() {
            Ok(t) if t.kind() == &TokenKind::Newline => break,
            Err(_) => break,

            Ok(tok) => BinOp::from_token_kind(tok.kind())?,
        };

        let (l_bp, r_bp) = op.infix_binding_power();

        if l_bp < min_bp {
            break;
        }

        s.advance().unwrap();

        let rhs = expr_bp(s, r_bp)?;

        lhs = Expr::BinaryOp(BinOpExpr {
            left: Box::new(lhs),
            op,
            right: Box::new(rhs),
        })
    }

    Ok(lhs)
}

fn atom_expr(s: &mut Scanner) -> Result<Expr> {
    match s.peek()?.kind() {
        TokenKind::LParen => paren_fn_call_stmt(s),
        TokenKind::StringLit(_) => string_lit(s),
        TokenKind::IntLit(_) => int_lit(s),

        actual => Error::unexpected_token(actual),
    }
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
        other => Error::unexpected_token(other),
    }
}

fn int_lit(s: &mut Scanner) -> Result<Expr> {
    match s.advance()?.kind() {
        TokenKind::IntLit(i) => Ok(Expr::IntLit(*i)),
        other => Error::unexpected_token(other),
    }
}

#[derive(Debug)]
struct BinOpExpr {
    left: Box<Expr>,
    op: BinOp,
    right: Box<Expr>,
}

#[derive(Debug)]
enum BinOp {
    Plus,
    Minus,
    Star,
    Slash,
}

impl BinOp {
    pub fn from_token_kind(kind: &TokenKind) -> Result<Self> {
        let op = match kind {
            TokenKind::Plus => Self::Plus,
            TokenKind::Minus => Self::Minus,
            TokenKind::Star => Self::Star,
            TokenKind::Slash => Self::Slash,

            other => return Error::unexpected_token(other),
        };

        Ok(op)
    }

    pub fn infix_binding_power(&self) -> (u8, u8) {
        use BinOp::*;
        match self {
            Plus | Minus => (1, 2),
            Star | Slash => (3, 4),
        }
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
