use super::{
    scanner::Scanner,
    stmt::{stmt, Stmt},
    Error, Result,
};
use crate::TokenKind;

/// FnDecl
#[derive(Debug)]
pub enum Decl {
    Fn(FnDecl),
}
pub fn decl(s: &mut Scanner) -> Result<Decl> {
    s.attempt(|s| fn_decl(s).map(Decl::Fn))
}

/// Fn Ident () Block
#[derive(Debug)]
pub struct FnDecl {
    pub name: String,

    pub block: Block,
}
pub fn fn_decl(s: &mut Scanner) -> Result<FnDecl> {
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
