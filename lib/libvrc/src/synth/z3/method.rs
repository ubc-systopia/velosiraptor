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
use smt2::{Function, Smt2Context, Term};

// crate imports
use super::{expr, types};
use crate::ast::{AstNodeGeneric, Method};

pub fn add_methods(smt: &mut Smt2Context, methods: &[Method]) {
    smt.section(String::from("Methods"));

    for m in methods {
        if matches!(
            m.name.as_str(),
            "translate" | "matchflags" | "map" | "unmap" | "protect"
        ) {
            smt.comment(format!("skipping method {}, handled elsewhere", m.name));
            continue;
        }

        let mut f = Function::new(m.name.clone(), types::type_to_smt2(&m.rettype));
        f.add_comment(format!("Function: {}, {}", m.name, m.loc()));

        f.add_arg(String::from("st!0"), String::from("Model_t"));
        for a in m.args.iter() {
            f.add_arg(a.name.clone(), types::type_to_smt2(&a.ptype));
        }

        if let Some(stmt) = &m.stmts {
            f.add_body(expr::stmt_to_smt2(stmt, "st!0"));
        }

        // // add the requires as assert
        // let mut body = Vec::new();
        // for p in m.requires.iter() {
        //     body.push(RTerm::assert(expr::expr_to_rosette(p)));
        // }

        // // convert statements into rosette statements
        // if let Some(stmts) = &m.stmts {
        //     body.push(expr::stmt_to_rosette(stmts))
        // }

        smt.function(f);
    }
}

pub fn add_translate_or_match_flags_fn(smt: &mut Smt2Context, method: &Method) {
    smt.section(String::from("Goal Function"));

    let mut f = Function::new(method.name.clone(), types::type_to_smt2(&method.rettype));
    f.add_comment(format!("Function: {}, {}", method.name, method.loc()));

    f.add_arg(String::from("st!0"), String::from("Model_t"));
    for a in method.args.iter() {
        f.add_arg(a.name.clone(), types::type_to_smt2(&a.ptype));
    }

    if let Some(stmt) = &method.stmts {
        f.add_body(expr::stmt_to_smt2(stmt, "st!0"));
    }

    smt.function(f);

    // add the pre-requisites
    let name = format!("{}.pre", method.name);
    let mut f = Function::new(name, types::boolean());
    f.add_comment(format!(
        "Function Preconditions: {}, {}",
        method.name,
        method.loc()
    ));

    f.add_arg(String::from("st!0"), String::from("Model_t"));
    for a in method.args.iter() {
        f.add_arg(a.name.clone(), types::type_to_smt2(&a.ptype));
    }

    let expr = Term::Binary(true);
    let expr = method
        .requires
        .iter()
        .fold(expr, |e, p| Term::land(e, expr::expr_to_smt2(p, "st!0")));

    f.add_body(expr);
    smt.function(f);
}
