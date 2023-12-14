// use std::collections::HashMap;

// use crate::parser::{Block, Decl, Expr, FnCallStmt, FnDecl, Program, Stmt};

// struct Environment {
//     fns: HashMap<String, FnDecl>,
// }

// fn eval_program(p: Program) {
//     for decl in p.decls {
//         eval_decl(decl);
//     }
// }

// fn eval_decl(decl: Decl) {
//     match decl {
//         Decl::Fn(func) => eval_fn(func),
//     }
// }

// fn eval_fn(func: FnDecl) {
//     eval_block(func.block);
// }

// fn eval_block(block: Block) {
//     for stmt in block.stmts {
//         eval_stmt(stmt);
//     }
// }

// fn eval_stmt(stmt: Stmt) {
//     match stmt {
//         Stmt::FnCall(call) => eval_call(&call),
//         Stmt::Expr(_) => todo!(),
//     };
// }

// fn eval_call(call: &FnCallStmt) -> String {
//     let evaluated_args: Vec<_> = call.args.iter().map(eval_expr).collect();
//     match call.name.as_str() {
//         "print" => {
//             println!("{}", evaluated_args.join(""));
//             "".to_string()
//         }

//         "plus" => {
//             let sum: i32 = evaluated_args
//                 .iter()
//                 .map(|s| s.parse::<i32>().unwrap())
//                 .sum();

//             sum.to_string()
//         }

//         _ => todo!(),
//     }
// }

// fn eval_expr(expr: &Expr) -> String {
//     match expr {
//         Expr::FnCall(call) => eval_call(call),
//         Expr::StringLit(s) => s.to_string(),
//         Expr::IntLit(i) => todo!(),
//     }
// }
