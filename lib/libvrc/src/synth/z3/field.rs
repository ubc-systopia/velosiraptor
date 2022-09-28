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

use smt2::{Attribute, Function, Smt2Context, Sort, SortedVar, Term};

use super::types;
use crate::ast::{Field, InterfaceField};

fn add_field_common(smt: &mut Smt2Context, ctxt: &str, field: &Field) {
    // let mut dt = DataType::new(format!("{}Field.{}", ctxt, field.name), 0);
    // dt.add_comment(format!("Field: {}, {}", field.name, field.loc()));
    // dt.add_field(format!("{}Field.{}.val?", ctxt, field.name), types::num());
    // smt.datatype(dt);
    smt.comment(format!("Type for the {}Field.{}_t", ctxt, field.name));

    let fieldtype = format!("{}Field.{}_t", ctxt, field.name);
    smt.sort(Sort::new_def(fieldtype.clone(), types::num()));

    for s in &field.layout {
        smt.comment(format!(
            "Accessors for {}Field.{}.{}",
            ctxt, field.name, s.name
        ));

        // the get() function extracting the bit fields
        let s_get_fn_name = format!("{}Field.{}.{}.get!", ctxt, field.name, s.name);
        let mut f = Function::new(s_get_fn_name.clone(), types::num());
        f.add_arg(field.name.clone(), fieldtype.clone());
        smt.function(f);

        let e = Term::bveq(
            Term::fn_apply(s_get_fn_name.clone(), vec![Term::ident("x@".to_string())]),
            Term::bvand(
                Term::bvshr(Term::ident("x@".to_string()), Term::num(s.start)),
                Term::num(s.mask_value() >> s.start),
            ), // Term::bv_zero_extend(
               //     Term::bv_extract(Term::ident("x@".to_string()), s.start, s.end),
               //     64 - ((s.end + 1) - s.start),
               // )
        );
        let attrs = vec![Attribute::with_value(
            "pattern".to_string(),
            format!("({} x@)", s_get_fn_name),
        )];

        let e = Term::attributed(e, attrs);
        smt.assert(Term::forall(
            vec![SortedVar::new("x@".to_string(), fieldtype.clone())],
            e,
        ));

        // the set() function inserting the bit fields
        let s_set_fn_name = format!("{}Field.{}.{}.set!", ctxt, field.name, s.name);
        let mut f = Function::new(s_set_fn_name.clone(), fieldtype.clone());
        f.add_arg(field.name.clone(), fieldtype.clone());
        f.add_arg(field.name.clone(), types::num());
        smt.function(f);

        let e = Term::bveq(
            Term::fn_apply(
                s_set_fn_name.clone(),
                vec![Term::ident("x@".to_string()), Term::ident("v@".to_string())],
            ),
            Term::bvor(
                Term::bvand(Term::ident("x@".to_string()), Term::num(!(s.mask_value()))),
                Term::bvshl(
                    Term::bvand(
                        Term::ident("v@".to_string()),
                        Term::num(s.mask_value() >> s.start),
                    ),
                    Term::num(s.start),
                ),
            ),
        );
        let attrs = vec![Attribute::with_value(
            "pattern".to_string(),
            format!("({} x@ v@)", s_set_fn_name),
        )];

        let e = Term::attributed(e, attrs);
        smt.assert(Term::forall(
            vec![
                SortedVar::new("x@".to_string(), fieldtype.clone()),
                SortedVar::new("v@".to_string(), types::num()),
            ],
            e,
        ));
    }
}

pub fn add_iface_field(smt: &mut Smt2Context, field: &InterfaceField) {
    add_field_common(smt, "IFace", &field.field);
}

pub fn add_state_field(smt: &mut Smt2Context, field: &Field) {
    add_field_common(smt, "State", field);
}

fn add_field_accessors_common(smt: &mut Smt2Context, ctxt: &str, field: &Field) {
    for slice in &field.layout {
        let name = format!("{}.{}.{}.get!", ctxt, field.name, slice.name);
        let mut f = Function::new(name, types::num());
        f.add_arg(String::from("st"), format!("{}_t", ctxt));

        let arg = Term::ident(String::from("st"));
        let st = Term::fn_apply(format!("{}.{}.get!", ctxt, field.name), vec![arg]);
        let e = Term::fn_apply(
            format!("{}Field.{}.{}.get!", ctxt, field.name, slice.name),
            vec![st],
        );
        f.add_body(e);
        smt.function(f);

        let name = format!("{}.{}.{}.set!", ctxt, field.name, slice.name);
        let mut f = Function::new(name, format!("{}_t", ctxt));
        f.add_arg(String::from("st"), format!("{}_t", ctxt));
        f.add_arg(String::from("val"), types::num());

        let arg = Term::ident(String::from("st"));
        let arg2 = Term::ident(String::from("val"));

        let fld = Term::fn_apply(format!("{}.{}.get!", ctxt, field.name), vec![arg.clone()]);
        let st = Term::fn_apply(
            format!("{}Field.{}.{}.set!", ctxt, field.name, slice.name),
            vec![fld, arg2],
        );
        let e = Term::fn_apply(format!("{}.{}.set!", ctxt, field.name), vec![arg, st]);
        f.add_body(e);
        smt.function(f);
    }
}

pub fn add_iface_field_accessors(smt: &mut Smt2Context, field: &InterfaceField) {
    add_field_accessors_common(smt, "IFace", &field.field);
}

pub fn add_state_field_accessors(smt: &mut Smt2Context, field: &Field) {
    add_field_accessors_common(smt, "State", field);
}
