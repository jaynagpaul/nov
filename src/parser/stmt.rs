use crate::TokenKind;

use super::{
    expr::{atom_exprs, expr, Expr},
    scanner::Scanner,
    Error, Result,
};

/// fn_call_stmt | expr
#[derive(Debug)]
pub enum Stmt {
    FnCall(FnCallStmt),
    Expr(Expr),
}
pub fn stmt(s: &mut Scanner) -> Result<Stmt> {
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
pub fn fn_call_stmt(s: &mut Scanner) -> Result<FnCallStmt> {
    let name = match s.advance()?.kind() {
        TokenKind::Ident(name) => name.to_string(),
        actual => return Error::unexpected_token(actual),
    };

    let args = atom_exprs(s)?;

    Ok(FnCallStmt { name, args })
}
