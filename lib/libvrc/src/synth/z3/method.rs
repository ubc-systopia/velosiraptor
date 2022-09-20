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
use smt2::{Function, Smt2Context, SortedVar, Term};

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

        smt.function(f);
    }
}

pub fn add_translate_or_match_flags_fn(smt: &mut Smt2Context, method: &Method) {
    let mut f = Function::new(method.name.clone(), types::type_to_smt2(&method.rettype));
    f.add_comment(format!(
        "Function: {}, {}",
        method.name,
        method.loc().input_sourcepos()
    ));

    f.add_arg(String::from("st!0"), String::from("Model_t"));
    for a in method.args.iter() {
        f.add_arg(a.name.clone(), types::type_to_smt2(&a.ptype));
    }

    if let Some(stmt) = &method.stmts {
        f.add_body(expr::stmt_to_smt2(stmt, "st!0"));
    }

    smt.function(f);

    // add the state pre-conditions of the function
    // this includes only pre-conditions that have state references.

    for (i, pre) in method
        .requires
        .iter()
        .filter(|p| p.has_state_references())
        .enumerate()
    {
        let name = format!("{}.pre.{}", method.name, i);
        let mut f = Function::new(name, types::boolean());
        f.add_comment(format!(
            "Function Preconditions part {}: {}, {}",
            i,
            method.name,
            method.loc().input_sourcepos()
        ));

        f.add_arg(String::from("st!0"), String::from("Model_t"));
        for a in method.args.iter() {
            f.add_arg(a.name.clone(), types::type_to_smt2(&a.ptype));
        }

        f.add_body(expr::expr_to_smt2(pre, "st!0"));
        smt.function(f);
    }

    let name = format!("{}.pre", method.name);
    let mut f = Function::new(name, types::boolean());
    f.add_comment(format!(
        "Function Preconditions: {}, {}",
        method.name,
        method.loc().input_sourcepos()
    ));

    f.add_arg(String::from("st!0"), String::from("Model_t"));
    for a in method.args.iter() {
        f.add_arg(a.name.clone(), types::type_to_smt2(&a.ptype));
    }

    let expr = Term::Binary(true);
    let expr = method
        .requires
        .iter()
        .filter(|p| p.has_state_references())
        .fold(expr, |e, p| Term::land(e, expr::expr_to_smt2(p, "st!0")));

    f.add_body(expr);
    smt.function(f);

    // add the assumptions on the function parameters
    // this includes only pre-conditions that do not have state references
    let name = format!("{}.assms", method.name);
    let mut f = Function::new(name, types::boolean());
    f.add_comment(format!(
        "Function Assumptions: {}, {}",
        method.name,
        method.loc().input_sourcepos()
    ));

    f.add_arg(String::from("st!0"), String::from("Model_t"));
    for a in method.args.iter() {
        f.add_arg(a.name.clone(), types::type_to_smt2(&a.ptype));
    }

    // add the type constraints on the function parameters
    let a = method.args.iter().fold(Term::Binary(true), |e, a| {
        Term::land(e, types::type_to_assms_fn(&a.ptype, a.name.clone()))
    });

    let expr = method
        .requires
        .iter()
        .filter(|p| !p.has_state_references())
        .fold(a, |e, p| Term::land(e, expr::expr_to_smt2(p, "st!0")));

    f.add_body(expr);

    smt.function(f);
}

pub fn add_translate_result_check(smt: &mut Smt2Context, method: &Method) {
    let fname = format!("{}.result", method.name);
    let mut f = Function::new(fname, types::boolean());
    f.add_comment(format!("Checking the {} function result", method.name));

    f.add_arg(String::from("st!0"), String::from("Model_t"));
    for a in method.args.iter() {
        f.add_arg(a.name.clone(), types::type_to_smt2(&a.ptype));
    }

    let varstr = "i!0".to_string();
    let forallvars = vec![SortedVar::new(varstr.clone(), types::size())];

    // forall i | 0 <= i < size :: translate (st!0, va + i) == pa + i
    // forall i :: 0 <= i < size ==> translate (st!0, va + i) == pa + i
    let constr = Term::land(
        Term::bvge(Term::num(0), Term::ident(varstr.clone())),
        Term::bvlt(Term::ident(varstr.clone()), Term::ident("sz".to_string())),
    );

    let mut args = vec![Term::ident(String::from("st!0"))];
    for a in &method.args {
        args.push(Term::bvadd(
            Term::ident(a.name.clone()),
            Term::ident(varstr.clone()),
        ));
    }

    let check = Term::bveq(
        Term::fn_apply(method.name.clone(), args),
        Term::bvadd(Term::ident(String::from("pa")), Term::ident(varstr)),
    );

    let body = Term::forall(forallvars, constr.implies(check));
    f.add_body(body);

    smt.function(f);
}

pub fn add_map_unmap_protect_assms(smt: &mut Smt2Context, method: &Method) {
    let fname = format!("{}.assms", method.name);

    let mut f = Function::new(fname, types::boolean());
    f.add_comment(format!(
        "Function Assumptions: {}, {}",
        method.name,
        method.loc().input_sourcepos()
    ));

    f.add_arg(String::from("st!0"), String::from("Model_t"));
    for a in method.args.iter() {
        f.add_arg(a.name.clone(), types::type_to_smt2(&a.ptype));
    }

    // add the type constraints on the function parameters
    let a = method.args.iter().fold(Term::Binary(true), |e, a| {
        Term::land(e, types::type_to_assms_fn(&a.ptype, a.name.clone()))
    });

    let expr = method
        .requires
        .iter()
        .filter(|p| !p.has_state_references())
        .fold(a, |e, p| Term::land(e, expr::expr_to_smt2(p, "st!0")));

    f.add_body(expr);

    smt.function(f);
}
