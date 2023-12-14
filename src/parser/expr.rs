use crate::TokenKind;

use super::{
    scanner::Scanner,
    stmt::{fn_call_stmt, FnCallStmt},
    Error, Result,
};

/// atom_expr atom_expr+
pub fn atom_exprs(s: &mut Scanner) -> Result<Vec<Expr>> {
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

pub fn expr(s: &mut Scanner) -> Result<Expr> {
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
