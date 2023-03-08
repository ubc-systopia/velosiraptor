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

//! Model Synthesis Module: Z3

use super::expr::{expr_to_smt2, p2p};
use super::types;

use smt2::{DataType, Function, Smt2Context, Term, VarBinding};
use velosiast::ast::{
    VelosiAstExpr, VelosiAstField, VelosiAstInterface, VelosiAstInterfaceAction, VelosiAstState,
    VelosiAstUnitSegment,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Constants
////////////////////////////////////////////////////////////////////////////////////////////////////

pub const IFACE_PREFIX: &str = "IFace";
pub const STATE_PREFIX: &str = "State";
pub const MODEL_PREFIX: &str = "Model";
pub const WBUFFER_PREFIX: &str = "WBuffer";

////////////////////////////////////////////////////////////////////////////////////////////////////
// Model
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Adds the model definition to the context
pub fn add_model_def(smt: &mut Smt2Context, unit: &VelosiAstUnitSegment) {
    add_model(smt);
    add_model_state_accessors(smt, &unit.state);
    add_model_iface_accessors(smt, &unit.interface);
    add_model_wbuffer_accessors(smt, &unit.interface);
    add_actions(smt, &unit.interface)
}

fn add_model(smt: &mut Smt2Context) {
    smt.section(String::from("Model"));
    let mut dt = DataType::new(MODEL_PREFIX.to_string(), 0);
    dt.add_comment("Model Definition".to_string());
    dt.add_field(format!("{MODEL_PREFIX}.{STATE_PREFIX}"), types::state());
    dt.add_field(format!("{MODEL_PREFIX}.{IFACE_PREFIX}"), types::iface());
    dt.add_field(format!("{MODEL_PREFIX}.{WBUFFER_PREFIX}"), types::wbuffer());

    let accessors = dt.to_field_accessor();
    smt.datatype(dt);

    smt.merge(accessors);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Model Accessors
////////////////////////////////////////////////////////////////////////////////////////////////////

use super::field::{
    field_get_fn_name, field_set_fn_name, field_slice_get_fn_name, field_slice_set_fn_name,
};

pub fn model_slice_get_fn_name(ctxt: &str, field: &str, slice: &str) -> String {
    let slice = slice.split('.').last().unwrap();
    let field = field.split('.').last().unwrap();
    format!("Model.{ctxt}.{field}.{slice}.get!")
}

pub fn model_slice_set_fn_name(ctxt: &str, field: &str, slice: &str) -> String {
    let slice = slice.split('.').last().unwrap();
    let field = field.split('.').last().unwrap();
    format!("Model.{ctxt}.{field}.{slice}.set!")
}

pub fn model_field_get_fn_name(ctxt: &str, field: &str) -> String {
    let field = field.split('.').last().unwrap();
    format!("Model.{ctxt}.{field}.get!")
}

pub fn model_field_set_fn_name(ctxt: &str, field: &str) -> String {
    let field = field.split('.').last().unwrap();
    format!("Model.{ctxt}.{field}.set!")
}

pub fn model_get_fn_name(ctxt: &str) -> String {
    format!("Model.{ctxt}.get!")
}

pub fn model_set_fn_name(ctxt: &str) -> String {
    format!("Model.{ctxt}.set!")
}

fn add_model_field_accessor(smt: &mut Smt2Context, ftype: &str, fieldname: &str) {
    //
    // Model Field Get
    //
    let name = model_field_get_fn_name(ftype, fieldname);
    let mut f = Function::new(name, types::field_type(ftype, fieldname));
    f.add_arg(String::from("st"), types::model());

    let arg = Term::ident(String::from("st"));
    let st = Term::fn_apply(model_get_fn_name(ftype), vec![arg]);
    let e = Term::fn_apply(field_get_fn_name(ftype, fieldname), vec![st]);
    f.add_body(e);
    smt.function(f);

    //
    // Model Field Set
    //
    let name = model_field_set_fn_name(ftype, fieldname);
    let mut f = Function::new(name, types::model());
    f.add_arg(String::from("st"), types::model());
    f.add_arg(String::from("val"), types::field_type(ftype, fieldname));

    let arg = Term::ident(String::from("st"));
    let arg2 = Term::ident(String::from("val"));

    let st = Term::fn_apply(model_get_fn_name(ftype), vec![arg.clone()]);

    let st = Term::fn_apply(field_set_fn_name(ftype, fieldname), vec![st, arg2]);
    let e = Term::fn_apply(model_set_fn_name(ftype), vec![arg, st]);
    f.add_body(e);

    smt.function(f);
}

fn add_model_slice_accessor(smt: &mut Smt2Context, ftype: &str, fieldname: &str, slice: &str) {
    //
    // Model Field Slice Get
    //

    let name = model_slice_get_fn_name(ftype, fieldname, slice);
    let mut f = Function::new(name, types::num());
    f.add_arg(String::from("st"), types::model());

    let arg = Term::ident(String::from("st"));
    let st = Term::fn_apply(model_get_fn_name(ftype), vec![arg]);
    let e = Term::fn_apply(field_slice_get_fn_name(ftype, fieldname, slice), vec![st]);
    f.add_body(e);

    smt.function(f);

    //
    // Model Field Slice Set
    //

    let name = model_slice_set_fn_name(ftype, fieldname, slice);
    let mut f = Function::new(name, types::model());
    f.add_arg(String::from("st"), types::model());
    f.add_arg(String::from("val"), types::num());

    let arg = Term::ident(String::from("st"));
    let arg2 = Term::ident(String::from("val"));

    let st = Term::fn_apply(model_get_fn_name(ftype), vec![arg.clone()]);

    // get the state

    // the field update (State.pte_t Int) State.pte_t)
    let st = Term::fn_apply(
        field_slice_set_fn_name(ftype, fieldname, slice),
        vec![st, arg2],
    );

    let e = Term::fn_apply(model_set_fn_name(ftype), vec![arg, st]);
    f.add_body(e);

    smt.function(f);
}

fn add_model_wbuffer_slice_set(smt: &mut Smt2Context, fieldname: &str, slice: &str) {
    let name = model_slice_set_fn_name(WBUFFER_PREFIX, fieldname, slice);
    let mut f = Function::new(name, types::model());
    f.add_arg(String::from("st"), types::model());
    f.add_arg(String::from("val"), types::num());

    let arg = Term::ident(String::from("st"));
    let arg2 = Term::ident(String::from("val"));

    let st = Term::fn_apply(model_get_fn_name(WBUFFER_PREFIX), vec![arg.clone()]);
    let lambda = Term::fn_apply(
        "lambda".to_string(),
        vec![
            // TODO: hack using ident
            Term::ident("((m Model_t))".to_string()),
            Term::fn_apply(
                model_slice_set_fn_name(IFACE_PREFIX, fieldname, slice),
                vec![Term::ident("m".to_string()), arg2],
            ),
        ],
    );

    let st = Term::fn_apply("insert".to_string(), vec![lambda, st]);
    let e = Term::fn_apply(model_set_fn_name(WBUFFER_PREFIX), vec![arg, st]);
    f.add_body(e);

    smt.function(f);
}

fn add_model_wbuffer_field_set(smt: &mut Smt2Context, fieldname: &str) {
    let name = model_field_set_fn_name(WBUFFER_PREFIX, fieldname);
    let mut f = Function::new(name, types::model());
    f.add_arg(String::from("st"), types::model());
    f.add_arg(
        String::from("val"),
        types::field_type(IFACE_PREFIX, fieldname),
    );

    let arg = Term::ident(String::from("st"));
    let arg2 = Term::ident(String::from("val"));

    let st = Term::fn_apply(model_get_fn_name(WBUFFER_PREFIX), vec![arg.clone()]);
    // TODO: hack using ident
    let lambda = Term::fn_apply(
        "lambda".to_string(),
        vec![
            Term::ident("((m Model_t))".to_string()),
            Term::fn_apply(
                model_field_set_fn_name(IFACE_PREFIX, fieldname),
                vec![Term::ident("m".to_string()), arg2],
            ),
        ],
    );

    let st = Term::fn_apply("insert".to_string(), vec![lambda, st]);
    let e = Term::fn_apply(model_set_fn_name(WBUFFER_PREFIX), vec![arg, st]);
    f.add_body(e);

    smt.function(f);
}

fn add_model_state_accessors(smt: &mut Smt2Context, state: &VelosiAstState) {
    smt.section(String::from("Model State Accessors"));
    for f in state.fields() {
        smt.subsection(format!("state field: {}", f.ident()));
        add_model_field_accessor(smt, STATE_PREFIX, f.ident());

        for s in f.layout_as_slice() {
            add_model_slice_accessor(smt, STATE_PREFIX, f.ident(), s.ident());
        }
    }
}

fn add_model_iface_accessors(smt: &mut Smt2Context, iface: &VelosiAstInterface) {
    smt.section(String::from("Model Interface Accessors"));

    for f in iface.fields() {
        smt.subsection(format!("interface field: {}", f.ident()));
        add_model_field_accessor(smt, IFACE_PREFIX, f.ident());
        for s in f.layout() {
            add_model_slice_accessor(smt, IFACE_PREFIX, f.ident(), s.ident());
        }
        // add the full field accessor
    }
}

fn add_model_wbuffer_accessors(smt: &mut Smt2Context, iface: &VelosiAstInterface) {
    smt.section(String::from("Model Write Buffer Accessors"));

    for f in iface.fields() {
        smt.subsection(format!("write buffer field: {}", f.ident()));
        add_model_wbuffer_field_set(smt, f.ident());

        for s in f.layout() {
            add_model_wbuffer_slice_set(smt, f.ident(), s.ident());
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Actions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn action_fn_name(fieldname: &str, ty: &str) -> String {
    let fieldname = fieldname.split('.').last().unwrap();
    format!("{MODEL_PREFIX}.{IFACE_PREFIX}.{fieldname}.{ty}action!")
}

fn add_field_action(
    smt: &mut Smt2Context,
    actions: &[VelosiAstInterfaceAction],
    fieldname: &str,
    ty: &str,
    _fieldwidth: u64,
) {
    let name = action_fn_name(fieldname, ty);
    let mut f = Function::new(name, types::model());
    f.add_arg(String::from("st"), types::model());
    f.add_comment(format!("performs the write actions of {fieldname}"));

    let mut defs = Vec::new();
    let mut stvar = String::from("st");

    // body = Term::letexpr(vec![VarBinding::new(newvar.clone(), f)], Term::ident(stvar));

    for (i, a) in actions.iter().enumerate() {
        let newvar = format!("st_{}", i + 1);

        let dst = match &a.dst {
            VelosiAstExpr::IdentLiteral(i) => {
                let mut s = i.path_split();
                match (s.next(), s.next(), s.next()) {
                    (Some(m), Some(f), Some(s)) => model_slice_set_fn_name(p2p(m), f, s),
                    (Some(m), Some(f), None) => model_field_set_fn_name(p2p(m), f),
                    e => panic!("unknown case: {:?}", e),
                }
            }
            _ => panic!("should not happen here! {}", &a.dst),
        };

        let src = expr_to_smt2(&a.src, &stvar);

        let fcall = Term::fn_apply(dst, vec![Term::ident(stvar.clone()), src]);

        defs.push(VarBinding::new(newvar.clone(), fcall));
        stvar = newvar;
    }

    let body = defs.iter().rev().fold(Term::ident(stvar), |acc, x| {
        Term::letexpr(vec![x.clone()], acc)
    });

    f.add_body(body);
    smt.function(f);
}

fn add_pop_action(smt: &mut Smt2Context) {
    let name = format!("{MODEL_PREFIX}.{WBUFFER_PREFIX}.popaction!");
    let mut f = Function::new(name, types::model());
    f.add_arg(String::from("st"), types::model());
    f.add_comment(format!(
        "takes one item off the write buffer and writes it to backing interface"
    ));

    let body = Term::letexpr(
        vec![VarBinding::new(
            "wb".to_string(),
            Term::fn_apply(
                model_get_fn_name(WBUFFER_PREFIX),
                vec![Term::ident("st".to_string())],
            ),
        )],
        Term::letexpr(
            vec![
                VarBinding::new(
                    "callback".to_string(),
                    Term::fn_apply("head".to_string(), vec![Term::ident("wb".to_string())]),
                ),
                VarBinding::new(
                    "new_wb".to_string(),
                    Term::fn_apply("tail".to_string(), vec![Term::ident("wb".to_string())]),
                ),
            ],
            Term::letexpr(
                vec![VarBinding::new(
                    "new_st".to_string(),
                    Term::fn_apply(
                        model_set_fn_name(WBUFFER_PREFIX),
                        vec![
                            Term::ident("st".to_string()),
                            Term::ident("new_wb".to_string()),
                        ],
                    ),
                )],
                Term::fn_apply(
                    "select".to_string(),
                    vec![
                        Term::ident("callback".to_string()),
                        Term::ident("new_st".to_string()),
                    ],
                ),
            ),
        ),
    );

    f.add_body(body);
    smt.function(f);
}

fn add_actions(smt: &mut Smt2Context, iface: &VelosiAstInterface) {
    smt.section(String::from("Actions"));
    for f in iface.fields() {
        smt.subsection(format!("interface field: {}", f.ident()));

        add_field_action(
            smt,
            f.write_actions_as_ref(),
            f.ident(),
            "write",
            f.size() * 8,
        );
        add_field_action(
            smt,
            f.read_actions_as_ref(),
            f.ident(),
            "read",
            f.size() * 8,
        );
    }

    add_pop_action(smt);
}
