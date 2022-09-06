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

//! State Synthesis Module: Rosette

// rosette language library imports
use smt2::{Expr, Function, Smt2File};

// crate imports
// use super::expr;
use crate::ast::{Method, Type};

fn type_to_smt2(ty: &Type) -> String {
    match ty {
        Type::Boolean => String::from("Bool"),
        Type::Integer => String::from("Int"),
        _ => panic!("unhandled type {}", ty),
    }
}


pub fn add_methods(smt: &mut Smt2File, methods: &[Method]) {
    smt.add_section(String::from("Methods"));

    for m in methods {
        match m.name.as_str() {
            "translate" => continue,
            "matchflags" => continue,
            "map" => continue,
            "unmap" => continue,
            "protect" => continue,
            _ => (),
        }

        let f = Function::new(
            m.name.clone(),
            type_to_smt2(&m.rettype),
        );

        // // let's add the arguments
        // let mut args = vec![String::from("st")];
        // for a in m.args.iter() {
        //     args.push(a.name.clone());
        // }

        // // add the requires as assert
        // let mut body = Vec::new();
        // for p in m.requires.iter() {
        //     body.push(RExpr::assert(expr::expr_to_rosette(p)));
        // }

        // // convert statements into rosette statements
        // if let Some(stmts) = &m.stmts {
        //     body.push(expr::stmt_to_rosette(stmts))
        // }

        smt.add_function(f);
    }

}