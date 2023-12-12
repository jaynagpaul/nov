mod eval;
mod parser;
mod scanner;
mod token;

pub use scanner::Scanner;
pub use token::{tokenize, Token, TokenKind};

fn main() {
    println!("Hello, world!");
}
