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
use rosettelang::{FunctionDef, RExpr, RosetteFile};

// crate imports
use crate::ast::{BitSlice, Field};

pub fn add_insert_extract(
    rkt: &mut RosetteFile,
    ftype: &str,
    field: &str,
    length: u64,
    bslice: &BitSlice,
) {
    let mask = ((1u128 << (bslice.end - bslice.start + 1)) - 1) as u64;
    let fieldsize = (length * 8) as u8;
    let varname = String::from("val");
    let oldname = String::from("old");

    // extract function
    let fname = format!("{}-fields-{}-{}-extract", ftype, field, bslice.name);
    let args = vec![varname.clone()];
    let body = RExpr::bvand(
        RExpr::bvshr(
            RExpr::var(varname.clone()),
            RExpr::num(fieldsize, bslice.start),
        ),
        RExpr::num(fieldsize, mask),
    );
    let mut fdef = FunctionDef::new(fname, args, vec![body]);
    fdef.add_comment(format!(
        "extract '{}' bits ({}..{}) from '{}' field value",
        bslice.name, bslice.start, bslice.end, field,
    ));
    rkt.add_function_def(fdef);

    // insert function
    let fname = format!("{}-fields-{}-{}-insert", ftype, field, bslice.name);
    let args = vec![oldname.clone(), varname.clone()];
    let body = RExpr::bvor(
        // mask old value
        RExpr::bvand(
            RExpr::var(oldname),
            // shift the mask to the start of the slice
            RExpr::num(fieldsize, !(mask << bslice.start)),
        ),
        // new value
        RExpr::bvshl(
            RExpr::bvand(RExpr::var(varname), RExpr::num(fieldsize, mask)),
            RExpr::num(fieldsize, bslice.start),
        ),
    );

    let mut fdef = FunctionDef::new(fname, args, vec![body]);
    fdef.add_comment(format!(
        "inserts '{}' bits ({}..{}) from '{}' field value",
        bslice.name, bslice.start, bslice.end, field
    ));
    rkt.add_function_def(fdef);
}

pub fn add_read_write_slice(rkt: &mut RosetteFile, ftype: &str, field: &str, bslice: &str) {
    let varname = String::from("val");
    let stname = String::from("st");

    let fname = format!("{}-fields-{}-{}-read", ftype, field, bslice);
    let args = vec![stname.clone()];
    let body = RExpr::fncall(
        format!("{}-fields-{}-{}-extract", ftype, field, bslice),
        vec![RExpr::fncall(
            format!("{}-fields-load-{}", ftype, field),
            vec![RExpr::var(stname.clone())],
        )],
    );
    let mut fdef = FunctionDef::new(fname, args, vec![body]);
    fdef.add_comment(format!(
        "reads '{}' bits from '{}' field value",
        field, bslice
    ));
    rkt.add_function_def(fdef);

    let fname = format!("{}-fields-{}-{}-write", ftype, field, bslice);
    let args = vec![stname.clone(), varname.clone()];
    let body = RExpr::fncall(
        format!("{}-fields-store-{}", ftype, field),
        vec![
            RExpr::var(stname.clone()),
            RExpr::fncall(
                format!("{}-fields-{}-{}-insert", ftype, field, bslice),
                vec![
                    RExpr::fncall(
                        format!("{}-fields-load-{}", ftype, field),
                        vec![RExpr::var(stname)],
                    ),
                    RExpr::var(varname),
                ],
            ),
        ],
    );

    let mut fdef = FunctionDef::new(fname, args, vec![body]);
    fdef.add_comment(format!(
        "writes '{}' bits from '{}' field value",
        field, bslice
    ));
    rkt.add_function_def(fdef);
}

pub fn add_slice_accessors(rkt: &mut RosetteFile, ftype: &str, field: &Field) {
    for b in &field.layout {
        rkt.add_subsection(format!("BitSlice: '{}.{}'", field.name, b.name));
        add_insert_extract(rkt, ftype, &field.name, field.length, b);
        add_read_write_slice(rkt, ftype, &field.name, &b.name);
    }
}
