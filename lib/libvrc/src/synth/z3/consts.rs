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

//! Const Synthesis Module: Rosette

// rosette language library imports
use smt2::{Smt2File, Expr};

// crate imports
use crate::ast;
use crate::ast::{ConstValue, Segment};

pub fn add_consts(smt: &mut Smt2File , unit: &Segment) {
    smt.add_section(format!("Constants for unit {}", unit.name));
    for c in unit.consts() {
        match &c.value {
            ConstValue::IntegerValue(u) => {
                smt.add_const(c.ident.clone(), String::from("Int"), Expr::num(*u))
            }
            ConstValue::BooleanValue(u) => {
                smt.add_const(c.ident.clone(), String::from("Int"), Expr::binary(*u))
            }
            ConstValue::IntegerExpr(ast::Expr::Number { value, .. }) => {
                smt.add_const(c.ident.clone(), String::from("Int"), Expr::num(*value))
            }
            x => unimplemented!("{:?}", x),
        }
    }
}
