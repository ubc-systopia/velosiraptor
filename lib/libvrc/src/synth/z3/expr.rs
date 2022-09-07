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

use crate::ast::{BinOp, Expr, Stmt, UnOp};
use smt2;

pub fn p2p(i: &str) -> &'static str {
    match i {
        "state" => "State",
        "interface" => "IFace",
        _ => panic!("uknown case: {}", i),
    }
}

pub fn expr_to_smt2(e: &Expr, stvar: &str) -> smt2::Expr {
    use Expr::*;
    match e {
        Expr::Identifier { path, .. } => {
            if path.len() == 2 {
                let ident = format!("Model.{}.{}.get", p2p(&path[0]), path[1]);
                smt2::Expr::fn_apply(ident, vec![smt2::Expr::ident(stvar.to_string())])
            } else if path.len() == 3 {
                let ident = format!("Model.{}.{}.{}.get", p2p(&path[0]), path[1], path[2]);
                smt2::Expr::fn_apply(ident, vec![smt2::Expr::ident(stvar.to_string())])
            } else {
                panic!("unexpected identifier lenght");
            }
        }
        Number { value, .. } => smt2::Expr::num(*value),
        Boolean { value, .. } => smt2::Expr::binary(*value),
        BinaryOperation { op, lhs, rhs, .. } => {
            let lhs = expr_to_smt2(lhs, stvar);
            let rhs = expr_to_smt2(rhs, stvar);
            match op {
                BinOp::And => smt2::Expr::bvand(lhs, rhs),
                BinOp::Or => smt2::Expr::bvor(lhs, rhs),
                BinOp::LShift => smt2::Expr::bvshl(lhs, rhs),
                BinOp::RShift => smt2::Expr::bvshr(lhs, rhs),
                BinOp::Eq => smt2::Expr::bveq(lhs, rhs),
                BinOp::Plus => smt2::Expr::bvadd(lhs, rhs),
                BinOp::Lt => smt2::Expr::bvlt(lhs, rhs),
                BinOp::Le => smt2::Expr::bvle(lhs, rhs),
                BinOp::Ge => smt2::Expr::bvge(lhs, rhs),
                BinOp::Gt => smt2::Expr::bvgt(lhs, rhs),
                BinOp::Ne => smt2::Expr::bvne(lhs, rhs),
                BinOp::Minus => smt2::Expr::bvsub(lhs, rhs),
                BinOp::Land => smt2::Expr::land(lhs, rhs),
                BinOp::Lor => smt2::Expr::lor(lhs, rhs),
                _ => {
                    println!("{:?}", op);
                    unimplemented!()
                }
            }
        }
        UnaryOperation { op, val, .. } => {
            let val = expr_to_smt2(val, stvar);
            match op {
                UnOp::Not => smt2::Expr::bvnot(val),
                UnOp::LNot => smt2::Expr::lnot(val),
                _ => {
                    println!("{:?}", op);
                    unimplemented!()
                }
            }
        }
        FnCall { path, args, .. } => {
            if path.len() != 1 {
                panic!("unexpected identifier lenght");
            }
            panic!("handle me!");
            let mut fnargs = vec![];
            // for a in args {
            //     fnargs.push(expr_to_rosette(a))
            // }
            smt2::Expr::fn_apply(path[0].clone(), fnargs)
        }
        Slice { .. } => unimplemented!(),
        Element { .. } => unimplemented!(),
        Range { .. } => unimplemented!(),
        Quantifier { .. } => unimplemented!(),
    }
}
