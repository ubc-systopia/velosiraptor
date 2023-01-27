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

use std::rc::Rc;

use smt2::{Attribute, Function, Smt2Context, Sort, SortedVar, Term};
use velosiast::ast::{
    VelosiAstFieldSlice, VelosiAstIdentifier, VelosiAstInterfaceField, VelosiAstStateField,
};

use super::types;
use super::velosimodel::{IFACE_PREFIX, STATE_PREFIX};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Field Definitions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn field_slice_extract_fn_name(ctxt: &str, field: &str, slice: &str) -> String {
    let sname = slice.split('.').last().unwrap();
    let field = field.split('.').last().unwrap();
    format!("{ctxt}Field.{field}.{sname}.get!")
}

fn field_slice_insert_fn_name(ctxt: &str, field: &str, slice: &str) -> String {
    let sname = slice.split('.').last().unwrap();
    let field = field.split('.').last().unwrap();
    format!("{ctxt}Field.{field}.{sname}.set!")
}

pub fn field_slice_get_fn_name(ctxt: &str, field: &str, slice: &str) -> String {
    let sname = slice.split('.').last().unwrap();
    let field = field.split('.').last().unwrap();
    format!("{ctxt}.{field}.{sname}.get!")
}

pub fn field_slice_set_fn_name(ctxt: &str, field: &str, slice: &str) -> String {
    let sname = slice.split('.').last().unwrap();
    let field = field.split('.').last().unwrap();
    format!("{ctxt}.{field}.{sname}.set!")
}

pub fn field_get_fn_name(ctxt: &str, field: &str) -> String {
    let field = field.split('.').last().unwrap();
    format!("{ctxt}.{field}.get!")
}

pub fn field_set_fn_name(ctxt: &str, field: &str) -> String {
    let field = field.split('.').last().unwrap();
    format!("{ctxt}.{field}.set!")
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Field Definitions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// adds the field type definition and adds accessors for the field type
fn add_field_common(
    smt: &mut Smt2Context,
    ident: &VelosiAstIdentifier,
    layout: &[Rc<VelosiAstFieldSlice>],
) {
    let mut identsplit = ident.path_split();
    let (ctxt, fieldname) = match (identsplit.next(), identsplit.next()) {
        (Some("state"), Some(name)) => (STATE_PREFIX, name),
        (Some("interface"), Some(name)) => (IFACE_PREFIX, name),
        _ => panic!("Invalid field name: {}", ident),
    };

    //
    // Step 1:  declare the sort (fieldtype), basically a typedef bv64 FieldName_t
    //
    // TODO: currently this is using a 64-bit bitvector, but we should take the size
    //       from the field into account.
    //
    let fieldtype = types::field_type(ctxt, fieldname);
    smt.comment(format!("Type for the {fieldtype}"));
    smt.sort(Sort::new_def(fieldtype.clone(), types::num()));

    //
    // Step 2: for each slice in the layout, add an extract/insert function
    //
    for s in layout {
        smt.comment(format!(
            "Accessors for {}Field.{}.{}",
            ctxt,
            fieldname,
            s.ident()
        ));

        //
        // Step 2.1.1: Add the accessor function definition (*.get!)
        //
        let s_get_fn_name = field_slice_extract_fn_name(ctxt, fieldname, s.ident());
        let mut f = Function::new(s_get_fn_name.clone(), types::num());
        f.add_arg(fieldname.to_string(), fieldtype.clone());
        smt.function(f);

        //
        // Step 2.1.2: Assert the function body thorugh equivalence
        //
        let e = Term::bveq(
            Term::fn_apply(s_get_fn_name.clone(), vec![Term::ident("x@".to_string())]),
            Term::bvand(
                Term::bvshr(Term::ident("x@".to_string()), Term::num(s.start)),
                Term::num(s.mask() >> s.start),
            ),
        );
        let attrs = vec![Attribute::with_value(
            "pattern".to_string(),
            format!("({s_get_fn_name} x@)"),
        )];

        let e = Term::attributed(e, attrs);
        smt.assert(Term::forall(
            vec![SortedVar::new("x@".to_string(), fieldtype.clone())],
            e,
        ));

        //
        // Step 2.2: Add the Accessor function (*.get!)
        //

        let s_set_fn_name = field_slice_insert_fn_name(ctxt, fieldname, s.ident());
        let mut f = Function::new(s_set_fn_name.clone(), fieldtype.clone());
        f.add_arg(fieldname.to_string(), fieldtype.clone());
        f.add_arg(fieldname.to_string(), types::num());
        smt.function(f);

        //
        // Step 2.2.2: Assert the function body thorugh equivalence
        //

        let e = Term::bveq(
            Term::fn_apply(
                s_set_fn_name.clone(),
                vec![Term::ident("x@".to_string()), Term::ident("v@".to_string())],
            ),
            Term::bvor(
                Term::bvand(Term::ident("x@".to_string()), Term::num(!(s.mask()))),
                Term::bvshl(
                    Term::bvand(
                        Term::ident("v@".to_string()),
                        Term::num(s.mask() >> s.start),
                    ),
                    Term::num(s.start),
                ),
            ),
        );
        let attrs = vec![Attribute::with_value(
            "pattern".to_string(),
            format!("({s_set_fn_name} x@ v@)"),
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

pub fn add_iface_field(smt: &mut Smt2Context, field: &VelosiAstInterfaceField) {
    use VelosiAstInterfaceField::*;
    match field {
        Memory(f) => add_field_common(smt, &f.ident, f.layout.as_slice()),
        Register(f) => add_field_common(smt, &f.ident, f.layout.as_slice()),
        Mmio(f) => add_field_common(smt, &f.ident, f.layout.as_slice()),
    }
}

pub fn add_state_field(smt: &mut Smt2Context, field: &VelosiAstStateField) {
    use VelosiAstStateField::*;
    match field {
        Memory(f) => add_field_common(smt, &f.ident, f.layout.as_slice()),
        Register(f) => add_field_common(smt, &f.ident, f.layout.as_slice()),
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Field Accessors
////////////////////////////////////////////////////////////////////////////////////////////////////

// fn add_field_accessors_common(smt: &mut Smt2Context, ctxt: &str, field: &Field) {

/// This function adds direct accessors
fn add_field_accessors_common(
    smt: &mut Smt2Context,
    ident: &VelosiAstIdentifier,
    layout: &[Rc<VelosiAstFieldSlice>],
) {
    let mut identsplit = ident.path_split();
    let (ctxt, fieldname) = match (identsplit.next(), identsplit.next()) {
        (Some("state"), Some(name)) => (STATE_PREFIX, name),
        (Some("interface"), Some(name)) => (IFACE_PREFIX, name),
        _ => panic!("Invalid field name: {}", ident),
    };

    let ctxttype = types::ctxt(ctxt);

    for slice in layout {
        let name = field_slice_get_fn_name(ctxt, fieldname, slice.ident());

        let mut f = Function::new(name, types::num());
        f.add_arg(String::from("st"), ctxttype.clone());

        let arg = Term::ident(String::from("st"));
        let st = Term::fn_apply(field_get_fn_name(ctxt, fieldname), vec![arg]);
        let e = Term::fn_apply(
            field_slice_extract_fn_name(ctxt, fieldname, slice.ident()),
            vec![st],
        );
        f.add_body(e);
        smt.function(f);

        let name = field_slice_set_fn_name(ctxt, fieldname, slice.ident());
        let mut f = Function::new(name, ctxttype.clone());
        f.add_arg(String::from("st"), ctxttype.clone());
        f.add_arg(String::from("val"), types::num());

        let arg = Term::ident(String::from("st"));
        let arg2 = Term::ident(String::from("val"));

        let fld = Term::fn_apply(field_get_fn_name(ctxt, fieldname), vec![arg.clone()]);
        let st = Term::fn_apply(
            field_slice_insert_fn_name(ctxt, fieldname, slice.ident()),
            vec![fld, arg2],
        );
        let e = Term::fn_apply(field_set_fn_name(ctxt, fieldname), vec![arg, st]);
        f.add_body(e);
        smt.function(f);
    }
}

pub fn add_iface_field_accessors(smt: &mut Smt2Context, field: &VelosiAstInterfaceField) {
    use VelosiAstInterfaceField::*;
    match field {
        Memory(f) => add_field_accessors_common(smt, &f.ident, f.layout.as_slice()),
        Register(f) => add_field_accessors_common(smt, &f.ident, f.layout.as_slice()),
        Mmio(f) => add_field_accessors_common(smt, &f.ident, f.layout.as_slice()),
    }
}

pub fn add_state_field_accessors(smt: &mut Smt2Context, field: &VelosiAstStateField) {
    use VelosiAstStateField::*;
    match field {
        Memory(f) => add_field_accessors_common(smt, &f.ident, f.layout.as_slice()),
        Register(f) => add_field_accessors_common(smt, &f.ident, f.layout.as_slice()),
    }
}
