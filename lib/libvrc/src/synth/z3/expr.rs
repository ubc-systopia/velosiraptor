// Velosiraptor Code Generator
//
//
// MIT License
//
// Copyright (c) 2021 Systopia Lab, Computer Science, University of British Columbia
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

//! Synthesis Module: Smt2 Expressions

use smt2;

use crate::ast::{BinOp, Expr, Stmt, UnOp};

pub fn p2p(i: &str) -> &'static str {
    match i {
        "state" => "State",
        "interface" => "IFace",
        _ => panic!("uknown case: {}", i),
    }
}

pub fn expr_to_smt2(e: &Expr, stvar: &str) -> smt2::Term {
    use Expr::*;
    match e {
        Expr::Identifier { path, .. } => {
            if path.len() == 1 {
                smt2::Term::ident(path[0].to_string())
            } else if path.len() == 2 {
                let ident = format!("Model.{}.{}.get", p2p(&path[0]), path[1]);
                smt2::Term::fn_apply(ident, vec![smt2::Term::ident(stvar.to_string())])
            } else if path.len() == 3 {
                let ident = format!("Model.{}.{}.{}.get", p2p(&path[0]), path[1], path[2]);
                smt2::Term::fn_apply(ident, vec![smt2::Term::ident(stvar.to_string())])
            } else {
                panic!("unexpected identifier lenght: {:?}", path);
            }
        }
        Number { value, .. } => smt2::Term::num(*value),
        Boolean { value, .. } => smt2::Term::binary(*value),
        BinaryOperation { op, lhs, rhs, .. } => {
            let lhs = expr_to_smt2(lhs, stvar);
            let rhs = expr_to_smt2(rhs, stvar);
            match op {
                BinOp::And => smt2::Term::bvand(lhs, rhs),
                BinOp::Or => smt2::Term::bvor(lhs, rhs),
                BinOp::LShift => smt2::Term::bvshl(lhs, rhs),
                BinOp::RShift => smt2::Term::bvshr(lhs, rhs),
                BinOp::Eq => smt2::Term::bveq(lhs, rhs),
                BinOp::Plus => smt2::Term::bvadd(lhs, rhs),
                BinOp::Lt => smt2::Term::bvlt(lhs, rhs),
                BinOp::Le => smt2::Term::bvle(lhs, rhs),
                BinOp::Ge => smt2::Term::bvge(lhs, rhs),
                BinOp::Gt => smt2::Term::bvgt(lhs, rhs),
                BinOp::Ne => smt2::Term::bvne(lhs, rhs),
                BinOp::Minus => smt2::Term::bvsub(lhs, rhs),
                BinOp::Land => smt2::Term::land(lhs, rhs),
                BinOp::Lor => smt2::Term::lor(lhs, rhs),
                _ => {
                    println!("{:?}", op);
                    unimplemented!()
                }
            }
        }
        UnaryOperation { op, val, .. } => {
            let val = expr_to_smt2(val, stvar);
            match op {
                UnOp::Not => smt2::Term::bvnot(val),
                UnOp::LNot => smt2::Term::lnot(val),
                _ => {
                    println!("{:?}", op);
                    unimplemented!()
                }
            }
        }
        FnCall { path, .. } => {
            if path.len() != 1 {
                panic!("unexpected identifier lenght");
            }
            panic!("handle me!");
            // let mut fnargs = vec![];
            // for a in args {
            //     fnargs.push(expr_to_rosette(a))
            // }
            //smt2::Term::fn_apply(path[0].clone(), fnargs)
        }
        Slice { .. } => unimplemented!(),
        Element { .. } => unimplemented!(),
        Range { .. } => unimplemented!(),
        Quantifier { .. } => unimplemented!(),
    }
}

pub fn stmt_to_smt2(stmt: &Stmt, stvar: &str) -> smt2::Term {
    match stmt {
        Stmt::Block { stmts, .. } => {
            if stmts.len() > 1 {
                panic!("only one statement per block is supported");
            }
            stmt_to_smt2(&stmts[0], stvar)
        }
        Stmt::Let { .. } => panic!("let not supported"),
        Stmt::IfElse { .. } => panic!("if-else not supported"),
        Stmt::Return { expr, .. } => expr_to_smt2(expr, stvar),
        Stmt::Assert { .. } => panic!("assert not supported"),
    }
}
