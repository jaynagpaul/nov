use crate::TokenKind;

use super::{
    expr::{atom_exprs, expr, Expr, FnCall},
    scanner::Scanner,
    Error, Result,
};

/// naked_fn_call | expr | let_stmt
#[derive(Debug)]
pub enum Stmt {
    Expr(Expr),
    Let(LetStmt),
}
pub fn stmt(s: &mut Scanner) -> Result<Stmt> {
    // enables print 'foo' instead of (print 'foo')
    let naked_fn_call = |s: &mut Scanner| Ok(Stmt::Expr(naked_fn_call(s)?));
    let expr_stmt = |s: &mut Scanner| Ok(Stmt::Expr(expr(s)?));
    let let_stmt = |s: &mut Scanner| Ok(Stmt::Let(let_stmt(s)?));

    let possible_stmts = [let_stmt, expr_stmt, naked_fn_call];
    s.attempt_all(&possible_stmts)
}

/// Ident Expr+
pub fn naked_fn_call(s: &mut Scanner) -> Result<Expr> {
    let name = match s.advance()?.kind() {
        TokenKind::Ident(name) => name.to_string(),
        actual => return Error::unexpected_token(actual),
    };

    let args = atom_exprs(s)?;

    Ok(Expr::FnCall(FnCall { name, args }))
}

/// let <name> = expr | naked_fn_call
#[derive(Debug)]
pub struct LetStmt {
    var_name: String,
    rhs: Expr,
}
pub fn let_stmt(s: &mut Scanner) -> Result<LetStmt> {
    dbg!("hey");
    let _ = s.match_kind(&TokenKind::Let);

    let var_name = match s.advance()?.kind() {
        TokenKind::Ident(name) => name.to_string(),
        actual => return Error::unexpected_token(actual),
    };

    let _ = s.match_kind(&TokenKind::Equals)?;

    let rhs_options = [naked_fn_call, expr];
    let rhs = s.attempt_all(&rhs_options)?;

    Ok(LetStmt { var_name, rhs })
}

#[cfg(test)]
mod tests {
    use expect_test::expect;

    use crate::parser::program;
    use crate::tokenize;

    use super::super::tests::check;
    use super::*;

    #[test]
    fn let_stmt() {
        let content = r#"let name = "nov" "#;
        let (tokens, errs) = tokenize(content);
        let mut scanner = Scanner::new(tokens);

        let stmt = stmt(&mut scanner);

        check(stmt, expect![[r#"
            Ok(
                Let(
                    LetStmt {
                        var_name: "name",
                        rhs: StringLit(
                            "nov",
                        ),
                    },
                ),
            )
        "#]]);
    }
}
