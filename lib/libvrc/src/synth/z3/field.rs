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

//! Field Synthesis Module: Z3

use crate::ast::{AstNodeGeneric, Field, InterfaceField};
use smt2::{DataType, Expr, Function, Smt2File};

// const BV_TYPE : &'static str = "(_ BitVec 32)";
const BV_TYPE: &'static str = "Int";

fn add_field_common(smt: &mut Smt2File, ctxt: &str, field: &Field) {
    let mut dt = DataType::new(format!("{}Field.{}", ctxt, field.name), 0);

    dt.add_comment(format!("Field: {}, {}", field.name, field.location()));

    for b in &field.layout {
        dt.add_field(
            format!("{}Field.{}.{}", ctxt, field.name, b.name),
            String::from(BV_TYPE),
        );
    }

    // dt.add_field(format!("{}.{}.val", ctxt, field.name), String::from(BV_TYPE));
    smt.add_datatype(dt);

    smt.add_comment(String::from("Field Invariant"));
}

pub fn add_iface_field(smt: &mut Smt2File, field: &InterfaceField) {
    add_field_common(smt, "IFace", &field.field);
}

pub fn add_state_field(smt: &mut Smt2File, field: &Field) {
    add_field_common(smt, "State", field);
}

fn add_field_accessors_common(smt: &mut Smt2File, ctxt: &str, field: &Field) {
    for slice in &field.layout {
        let name = format!("{}.{}.{}.get", ctxt, field.name, slice.name);
        let mut f = Function::new(name, String::from("Int"));
        f.add_arg(format!("{}_t", ctxt));

        let arg = Expr::ident(String::from("x!0"));
        let st = Expr::fn_apply(format!("{}.{}.get", ctxt, field.name), vec![arg]);
        let e = Expr::fn_apply(
            format!("{}Field.{}.{}.get", ctxt, field.name, slice.name),
            vec![st],
        );
        f.add_body(e);
        smt.add_function(f);

        let name = format!("{}.{}.{}.set", ctxt, field.name, slice.name);
        let mut f = Function::new(name, format!("{}_t", ctxt));
        f.add_arg(format!("{}_t", ctxt));
        f.add_arg(String::from("Int"));

        let arg = Expr::ident(String::from("x!0"));
        let arg2 = Expr::ident(String::from("x!1"));

        let fld = Expr::fn_apply(format!("{}.{}.get", ctxt, field.name), vec![arg.clone()]);
        let st = Expr::fn_apply(
            format!("{}Field.{}.{}.set", ctxt, field.name, slice.name),
            vec![fld, arg2],
        );
        let e = Expr::fn_apply(format!("{}.{}.set", ctxt, field.name), vec![arg, st]);
        f.add_body(e);
        smt.add_function(f);
    }
}

pub fn add_iface_field_accessors(smt: &mut Smt2File, field: &InterfaceField) {
    add_field_accessors_common(smt, "IFace", &field.field);
}

pub fn add_state_field_accessors(smt: &mut Smt2File, field: &Field) {
    add_field_accessors_common(smt, "State", &field);
}
