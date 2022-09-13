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

use crate::ast::Type;

use smt2::{Function, Smt2Context, Sort, Term};

pub const DEFAULT_BIT_WIDTH: u64 = 64;

pub fn model() -> String {
    String::from("Model_t")
}

pub fn num() -> String {
    String::from("Num")
}

pub fn boolean() -> String {
    String::from("Bool")
}

pub fn addr() -> String {
    "Addr_t".to_string()
}

pub fn vaddr() -> String {
    "VAddr_t".to_string()
}

pub fn paddr() -> String {
    "PAddr_t".to_string()
}

pub fn size() -> String {
    "Size_t".to_string()
}

pub fn flags() -> String {
    "Flags_t".to_string()
}

pub fn add_type_def(smt: &mut Smt2Context, name: String, sort: String) {
    let sort = Sort::new_def(name, sort);
    smt.sort(sort);
}

pub fn add_type_constraints(smt: &mut Smt2Context, name: String, maxbits: u64) {
    let fnname = format!("{}.assms", name);
    let mut f = Function::new(fnname, boolean());
    f.add_comment(format!("Type constraints {}", name));
    f.add_arg(String::from("v"), name);

    let body = if maxbits == DEFAULT_BIT_WIDTH {
        Term::binary(true)
    } else {
        let maxval = (1 << maxbits) - 1;
        Term::land(
            Term::bvge(Term::ident("v".to_string()), Term::num(0)),
            Term::bvle(Term::ident("v".to_string()), Term::num(maxval)),
        )
    };

    f.add_body(body);
    smt.function(f);
}

pub fn add_type_defs(smt: &mut Smt2Context, inaddr: u64, outaddr: u64) {
    smt.section(String::from("Type Definitions"));

    let default_sort = format!("(_ BitVec {})", DEFAULT_BIT_WIDTH);
    add_type_def(smt, num(), default_sort.clone());
    add_type_def(smt, addr(), default_sort.clone());
    add_type_def(smt, vaddr(), default_sort.clone());
    add_type_def(smt, paddr(), default_sort.clone());
    add_type_def(smt, size(), default_sort.clone());
    add_type_def(smt, flags(), default_sort);

    add_type_constraints(smt, addr(), DEFAULT_BIT_WIDTH);
    add_type_constraints(smt, vaddr(), inaddr);
    add_type_constraints(smt, paddr(), outaddr);
    add_type_constraints(smt, size(), std::cmp::min(inaddr, outaddr));
    add_type_constraints(smt, flags(), DEFAULT_BIT_WIDTH);
}

pub fn type_to_smt2(ty: &Type) -> String {
    match ty {
        Type::Boolean => boolean(),
        Type::Integer => num(),
        Type::Address => num(),
        Type::VirtualAddress => vaddr(),
        Type::PhysicalAddress => paddr(),
        Type::Flags => flags(),
        Type::Size => size(),
        _ => panic!("unhandled type {}", ty),
    }
}

pub fn type_to_assms_fn_name(ty: &Type) -> String {
    format!("{}.assms", type_to_smt2(ty))
}

pub fn type_to_assms_fn(ty: &Type, var: String) -> Term {
    let fname = type_to_assms_fn_name(ty);
    Term::fn_apply(fname, vec![Term::ident(var)])
}
