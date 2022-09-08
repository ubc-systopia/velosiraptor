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

use smt2::{DataType, Function, Smt2Context, Term};

use super::types;
use crate::ast::{AstNodeGeneric, Field, InterfaceField};

fn add_field_common(smt: &mut Smt2Context, ctxt: &str, field: &Field) {
    let mut dt = DataType::new(format!("{}Field.{}", ctxt, field.name), 0);

    dt.add_comment(format!("Field: {}, {}", field.name, field.loc()));

    for b in &field.layout {
        dt.add_field(
            format!("{}Field.{}.{}", ctxt, field.name, b.name),
            types::num(),
        );
    }

    // dt.add_field(format!("{}.{}.val", ctxt, field.name), String::from(BV_TYPE));
    smt.datatype(dt);

    smt.comment(String::from("Field Invariant"));
}

pub fn add_iface_field(smt: &mut Smt2Context, field: &InterfaceField) {
    add_field_common(smt, "IFace", &field.field);
}

pub fn add_state_field(smt: &mut Smt2Context, field: &Field) {
    add_field_common(smt, "State", field);
}

fn add_field_accessors_common(smt: &mut Smt2Context, ctxt: &str, field: &Field) {
    for slice in &field.layout {
        let name = format!("{}.{}.{}.get", ctxt, field.name, slice.name);
        let mut f = Function::new(name, types::num());
        f.add_arg(String::from("st"), format!("{}_t", ctxt));

        let arg = Term::ident(String::from("st"));
        let st = Term::fn_apply(format!("{}.{}.get", ctxt, field.name), vec![arg]);
        let e = Term::fn_apply(
            format!("{}Field.{}.{}.get", ctxt, field.name, slice.name),
            vec![st],
        );
        f.add_body(e);
        smt.function(f);

        let name = format!("{}.{}.{}.set", ctxt, field.name, slice.name);
        let mut f = Function::new(name, format!("{}_t", ctxt));
        f.add_arg(String::from("st"), format!("{}_t", ctxt));
        f.add_arg(String::from("val"), types::num());

        let arg = Term::ident(String::from("st"));
        let arg2 = Term::ident(String::from("val"));

        let fld = Term::fn_apply(format!("{}.{}.get", ctxt, field.name), vec![arg.clone()]);
        let st = Term::fn_apply(
            format!("{}Field.{}.{}.set", ctxt, field.name, slice.name),
            vec![fld, arg2],
        );
        let e = Term::fn_apply(format!("{}.{}.set", ctxt, field.name), vec![arg, st]);
        f.add_body(e);
        smt.function(f);
    }
}

pub fn add_iface_field_accessors(smt: &mut Smt2Context, field: &InterfaceField) {
    add_field_accessors_common(smt, "IFace", &field.field);
}

pub fn add_state_field_accessors(smt: &mut Smt2Context, field: &Field) {
    add_field_accessors_common(smt, "State", &field);
}
