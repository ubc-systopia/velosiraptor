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

//! Synthesis Module: Rosette Expressions

use rosettelang::{BVOp, RExpr};

use crate::ast::{BinOp, Expr};

fn bin_op_to_rosette(op: BinOp) -> BVOp {
    use BinOp::*;
    match op {
        Plus => unimplemented!(),
        Minus => unimplemented!(),
        Multiply => unimplemented!(),
        Divide => unimplemented!(),
        Modulo => unimplemented!(),
        LShift => unimplemented!(),
        RShift => unimplemented!(),
        And => unimplemented!(),
        Xor => unimplemented!(),
        Or => unimplemented!(),
        // boolean operators
        Eq => unimplemented!(),
        Ne => unimplemented!(),
        Lt => unimplemented!(),
        Gt => unimplemented!(),
        Le => unimplemented!(),
        Ge => unimplemented!(),
        Land => unimplemented!(),
        Lor => unimplemented!(),
        Implies => unimplemented!(),
    }
}

pub fn expr_to_rosette(e: &Expr) -> RExpr {
    use Expr::*;
    match e {
        Identifier { path, .. } => {
            if path.len() == 2 {
                let ident = format!("{}-load-{}", path[0], path[1]);
                RExpr::fncall(ident, vec![RExpr::var(String::from("st"))])
            } else if path.len() == 3 {
                let ident = format!("{}-{}-{}-read", path[0], path[1], path[0]);
                RExpr::fncall(ident, vec![RExpr::var(String::from("st"))])
            } else if path.len() == 1 {
                RExpr::var(path[0].clone())
            } else {
                panic!("unexpected identifier lenght");
            }
        }
        Number { value: u64, .. } => unimplemented!(),
        Boolean { value, .. } => unimplemented!(),
        BinaryOperation { op, lhs, rhs, .. } => {
            let lhs = expr_to_rosette(lhs);
            let rhs = expr_to_rosette(rhs);
            match op {
                BinOp::And => RExpr::bvand(lhs, rhs),
                BinOp::Or => RExpr::bvand(lhs, rhs),
                BinOp::LShift => RExpr::bvshl(lhs, rhs),
                BinOp::RShift => RExpr::bvshr(lhs, rhs),
                BinOp::Eq => RExpr::bveq(lhs, rhs),
                BinOp::Plus => RExpr::bvadd(lhs, rhs),
                BinOp::Lt => RExpr::bvlt(lhs, rhs),
                _ => {
                    println!("{:?}", op);
                    unimplemented!()
                }
            }
        }
        UnaryOperation { op, val, .. } => unimplemented!(),
        FnCall { path, args, .. } => {
            if path.len() != 1 {
                panic!("unexpected identifier lenght");
            }
            let mut fnargs = vec![RExpr::var(String::from("st"))];
            for a in args {
                fnargs.push(expr_to_rosette(a))
            }

            RExpr::fncall(path[0].clone(), fnargs)
        }
        Slice { .. } => unimplemented!(),
        Element { .. } => unimplemented!(),
        Range { .. } => unimplemented!(),
        Quantifier { .. } => unimplemented!(),
    }
}
