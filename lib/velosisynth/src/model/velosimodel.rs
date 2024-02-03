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

use std::rc::Rc;

use super::expr::{expr_to_smt2, p2p};
use super::{types, utils};

use smt2::{DataType, Function, MatchCase, Pattern, Smt2Context, SortedVar, Term, VarBinding};
use velosiast::ast::{
    VelosiAstExpr, VelosiAstField, VelosiAstIdentLiteralExpr, VelosiAstInterface,
    VelosiAstInterfaceAction, VelosiAstState, VelosiAstTypeInfo, VelosiAstUnitSegment,
};
use velosiast::VelosiAstInterfaceField;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Constants
////////////////////////////////////////////////////////////////////////////////////////////////////

pub const IFACE_PREFIX: &str = "IFace";
pub const STATE_PREFIX: &str = "State";
pub const MODEL_PREFIX: &str = "Model";
pub const WBUFFER_PREFIX: &str = "WBuffer";
pub const WBUFFER_ENTRY_PREFIX: &str = "WBufferEntry";
pub const LOCAL_VARS_PREFIX: &str = "LocalVars";

////////////////////////////////////////////////////////////////////////////////////////////////////
// Model
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Adds the model definition to the context
pub fn add_model_def(smt: &mut Smt2Context, unit: &VelosiAstUnitSegment, mem_model: bool) {
    add_model(smt, unit.ident(), mem_model);
    add_model_state_accessors(smt, unit.ident(), &unit.state);
    add_model_iface_accessors(smt, unit.ident(), &unit.interface);
    if mem_model {
        add_model_wbuffer_accessors(smt, unit.ident(), &unit.interface);
        add_model_local_vars_accessors(smt, unit.ident(), &unit.interface);
    }
    add_actions(smt, unit.ident(), &unit.interface, mem_model)
}

fn add_model(smt: &mut Smt2Context, prefix: &str, mem_model: bool) {
    smt.section(String::from("Model"));
    let mut dt = DataType::new(utils::with_prefix(prefix, MODEL_PREFIX), 0);
    dt.add_comment("Model Definition".to_string());
    dt.add_field(
        utils::with_prefix(prefix, &format!("{MODEL_PREFIX}.{STATE_PREFIX}")),
        types::state(prefix),
    );
    dt.add_field(
        utils::with_prefix(prefix, &format!("{MODEL_PREFIX}.{IFACE_PREFIX}")),
        types::iface(prefix),
    );

    if mem_model {
        dt.add_field(
            utils::with_prefix(prefix, &format!("{MODEL_PREFIX}.{WBUFFER_PREFIX}")),
            types::wbuffer(prefix),
        );
        dt.add_field(
            utils::with_prefix(prefix, &format!("{MODEL_PREFIX}.{LOCAL_VARS_PREFIX}")),
            types::iface(prefix),
        );
    }

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

pub fn model_slice_get_fn_name(prefix: &str, ctxt: &str, field: &str, slice: &str) -> String {
    let slice = slice.split('.').last().unwrap();
    let field = field.split('.').last().unwrap();
    utils::with_prefix(
        prefix,
        &format!("{MODEL_PREFIX}.{ctxt}.{field}.{slice}.get!"),
    )
}

pub fn model_slice_set_fn_name(prefix: &str, ctxt: &str, field: &str, slice: &str) -> String {
    let slice = slice.split('.').last().unwrap();
    let field = field.split('.').last().unwrap();
    utils::with_prefix(
        prefix,
        &format!("{MODEL_PREFIX}.{ctxt}.{field}.{slice}.set!"),
    )
}

pub fn model_field_get_fn_name(prefix: &str, ctxt: &str, field: &str) -> String {
    let field = field.split('.').last().unwrap();
    utils::with_prefix(prefix, &format!("{MODEL_PREFIX}.{ctxt}.{field}.get!"))
}

pub fn model_field_set_fn_name(prefix: &str, ctxt: &str, field: &str) -> String {
    let field = field.split('.').last().unwrap();
    utils::with_prefix(prefix, &format!("{MODEL_PREFIX}.{ctxt}.{field}.set!"))
}

pub fn model_get_fn_name(prefix: &str, ctxt: &str) -> String {
    utils::with_prefix(prefix, &format!("{MODEL_PREFIX}.{ctxt}.get!"))
}

pub fn model_set_fn_name(prefix: &str, ctxt: &str) -> String {
    utils::with_prefix(prefix, &format!("{MODEL_PREFIX}.{ctxt}.set!"))
}

fn add_model_field_accessor(
    smt: &mut Smt2Context,
    prefix: &str,
    ftype: &str,
    mtype: &str,
    fieldname: &str,
) {
    //
    // Model Field Get
    //
    let name = model_field_get_fn_name(prefix, mtype, fieldname);
    let mut f = Function::new(name, types::field_type(prefix, ftype, fieldname));
    f.add_arg(String::from("st"), types::model(prefix));

    let arg = Term::ident(String::from("st"));
    let st = Term::fn_apply(model_get_fn_name(prefix, mtype), vec![arg]);
    let e = Term::fn_apply(field_get_fn_name(prefix, ftype, fieldname), vec![st]);
    f.add_body(e);
    smt.function(f);

    //
    // Model Field Set
    //
    let name = model_field_set_fn_name(prefix, mtype, fieldname);
    let mut f = Function::new(name, types::model(prefix));
    f.add_arg(String::from("st"), types::model(prefix));
    f.add_arg(
        String::from("val"),
        types::field_type(prefix, ftype, fieldname),
    );

    let arg = Term::ident(String::from("st"));
    let arg2 = Term::ident(String::from("val"));

    let st = Term::fn_apply(model_get_fn_name(prefix, mtype), vec![arg.clone()]);

    let st = Term::fn_apply(field_set_fn_name(prefix, ftype, fieldname), vec![st, arg2]);
    let e = Term::fn_apply(model_set_fn_name(prefix, mtype), vec![arg, st]);
    f.add_body(e);

    smt.function(f);
}

fn add_model_slice_accessor(
    smt: &mut Smt2Context,
    prefix: &str,
    ftype: &str,
    mtype: &str,
    fieldname: &str,
    slice: &str,
) {
    //
    // Model Field Slice Get
    //

    let name = model_slice_get_fn_name(prefix, mtype, fieldname, slice);
    let mut f = Function::new(name, types::num(prefix));
    f.add_arg(String::from("st"), types::model(prefix));

    let arg = Term::ident(String::from("st"));
    let st = Term::fn_apply(model_get_fn_name(prefix, mtype), vec![arg]);
    let e = Term::fn_apply(
        field_slice_get_fn_name(prefix, ftype, fieldname, slice),
        vec![st],
    );
    f.add_body(e);

    smt.function(f);

    //
    // Model Field Slice Set
    //

    let name = model_slice_set_fn_name(prefix, mtype, fieldname, slice);
    let mut f = Function::new(name, types::model(prefix));
    f.add_arg(String::from("st"), types::model(prefix));
    f.add_arg(String::from("val"), types::num(prefix));

    let arg = Term::ident(String::from("st"));
    let arg2 = Term::ident(String::from("val"));

    let st = Term::fn_apply(model_get_fn_name(prefix, mtype), vec![arg.clone()]);

    // get the state

    // the field update (State.pte_t Int) State.pte_t)
    let st = Term::fn_apply(
        field_slice_set_fn_name(prefix, ftype, fieldname, slice),
        vec![st, arg2],
    );

    let e = Term::fn_apply(model_set_fn_name(prefix, mtype), vec![arg, st]);
    f.add_body(e);

    smt.function(f);
}

fn add_model_wbuffer_field_set(smt: &mut Smt2Context, prefix: &str, fieldname: &str) {
    let name = model_field_set_fn_name(prefix, WBUFFER_PREFIX, fieldname);
    let mut f = Function::new(name, types::model(prefix));
    f.add_arg(String::from("st"), types::model(prefix));
    f.add_arg(
        String::from("val"),
        types::field_type(prefix, IFACE_PREFIX, fieldname),
    );

    let arg = Term::ident(String::from("st"));
    let arg2 = Term::ident(String::from("val"));

    let st = Term::fn_apply(model_get_fn_name(prefix, WBUFFER_PREFIX), vec![arg.clone()]);
    let wbuffer_entry = Term::fn_apply(
        utils::with_prefix(prefix, WBUFFER_ENTRY_PREFIX),
        vec![Term::ident(types::field_tag_enum(fieldname)), arg2],
    );

    let st = smt2::seq::concat(vec![st, smt2::seq::unit(wbuffer_entry)]);
    let e = Term::fn_apply(model_set_fn_name(prefix, WBUFFER_PREFIX), vec![arg, st]);
    f.add_body(e);

    smt.function(f);
}

fn add_model_state_accessors(smt: &mut Smt2Context, prefix: &str, state: &VelosiAstState) {
    smt.section(String::from("Model State Accessors"));
    for f in state.fields() {
        smt.subsection(format!("state field: {}", f.ident()));
        add_model_field_accessor(smt, prefix, STATE_PREFIX, STATE_PREFIX, f.ident());

        for s in f.layout_as_slice() {
            add_model_slice_accessor(
                smt,
                prefix,
                STATE_PREFIX,
                STATE_PREFIX,
                f.ident(),
                s.ident(),
            );
        }
    }
}

fn add_model_iface_accessors(smt: &mut Smt2Context, prefix: &str, iface: &VelosiAstInterface) {
    smt.section(String::from("Model Interface Accessors"));

    for f in iface.fields() {
        smt.subsection(format!("interface field: {}", f.ident()));
        add_model_field_accessor(smt, prefix, IFACE_PREFIX, IFACE_PREFIX, f.ident());
        for s in f.layout() {
            add_model_slice_accessor(
                smt,
                prefix,
                IFACE_PREFIX,
                IFACE_PREFIX,
                f.ident(),
                s.ident(),
            );
        }
        // add the full field accessor
    }
}

fn add_model_wbuffer_accessors(smt: &mut Smt2Context, prefix: &str, iface: &VelosiAstInterface) {
    smt.section(String::from("Model Write Buffer Accessors"));

    for f in iface.fields() {
        smt.subsection(format!("write buffer field: {}", f.ident()));
        add_model_wbuffer_field_set(smt, prefix, f.ident());
    }
}

fn add_model_local_vars_accessors(smt: &mut Smt2Context, prefix: &str, iface: &VelosiAstInterface) {
    smt.section(String::from("Local Variable Accessors"));

    for f in iface.fields() {
        add_model_field_accessor(smt, prefix, IFACE_PREFIX, LOCAL_VARS_PREFIX, f.ident());
        for s in f.layout() {
            add_model_slice_accessor(
                smt,
                prefix,
                IFACE_PREFIX,
                LOCAL_VARS_PREFIX,
                f.ident(),
                s.ident(),
            );
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Actions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn action_fn_name(prefix: &str, ctxt: &str, fieldname: &str, ty: &str) -> String {
    let fieldname = fieldname.split('.').last().unwrap();
    format!("{prefix}.{MODEL_PREFIX}.{ctxt}.{fieldname}.{ty}action!")
}

fn add_field_action(
    smt: &mut Smt2Context,
    prefix: &str,
    actions: &[VelosiAstInterfaceAction],
    modelname: &str,
    fieldname: &str,
    ty: &str,
    _fieldwidth: u64,
) {
    let name = action_fn_name(prefix, modelname, fieldname, ty);
    let mut f = Function::new(name, types::model(prefix));
    f.add_arg(String::from("st"), types::model(prefix));
    f.add_comment(format!("performs the write actions of {fieldname}"));

    let mut defs = Vec::new();
    let mut stvar = String::from("st");

    // body = Term::letexpr(vec![VarBinding::new(newvar.clone(), f)], Term::ident(stvar));

    for (i, a) in actions.iter().enumerate() {
        let newvar = format!("st_{}", i + 1);

        let dst = match a.dst.as_ref() {
            VelosiAstExpr::IdentLiteral(i) => {
                let mut s = i.path_split();
                match (s.next(), s.next(), s.next()) {
                    (Some(m), Some(f), Some(s)) => model_slice_set_fn_name(prefix, p2p(m), f, s),
                    (Some(m), Some(f), None) => model_field_set_fn_name(prefix, p2p(m), f),
                    e => panic!("unknown case: {:?}", e),
                }
            }
            _ => panic!("should not happen here! {}", &a.dst),
        };

        let src = expr_to_smt2(prefix, &a.src, &stvar);

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

fn add_apply_entry_action(smt: &mut Smt2Context, prefix: &str, iface: &VelosiAstInterface) {
    let name = format!("{prefix}.{MODEL_PREFIX}.{WBUFFER_PREFIX}.applyentryaction!");
    let mut f = Function::new(name, types::model(prefix));
    f.add_arg(String::from("st"), types::model(prefix));
    f.add_arg(String::from("entry"), types::wbuffer_entry(prefix));
    f.add_comment("applies the given write buffer entry to the model, writing the value and applying the write action on the right field".to_string());

    let st = Term::ident(String::from("st"));
    let entry = Term::ident(String::from("entry"));
    let body = Term::Match(
        Box::new(Term::fn_apply(
            field_get_fn_name(prefix, WBUFFER_ENTRY_PREFIX, "tag"),
            vec![entry.clone()],
        )),
        iface
            .fields()
            .iter()
            .map(|field| field.ident())
            .map(|fieldname| {
                MatchCase::new(
                    Pattern::new(vec![types::field_tag_enum(fieldname)]),
                    Term::fn_apply(
                        format!("{prefix}.{MODEL_PREFIX}.{IFACE_PREFIX}.{fieldname}.writeaction!"),
                        vec![Term::fn_apply(
                            model_field_set_fn_name(prefix, IFACE_PREFIX, fieldname),
                            vec![
                                st.clone(),
                                Term::fn_apply(
                                    field_get_fn_name(prefix, WBUFFER_ENTRY_PREFIX, "val"),
                                    vec![entry.clone()],
                                ),
                            ],
                        )],
                    ),
                )
            })
            .collect(),
    );

    f.add_body(body);
    smt.function(f);
}

fn add_flush_action(smt: &mut Smt2Context, prefix: &str) {
    let name = format!("{prefix}.{MODEL_PREFIX}.{WBUFFER_PREFIX}.flushaction!");
    let mut f = Function::new(name, types::model(prefix));
    f.add_arg(String::from("st"), types::model(prefix));
    f.add_comment("flushes the write buffer, writing values back to the interface and applying their write actions".to_string());

    let st = Term::ident(String::from("st"));
    let body = Term::letexpr(
        vec![
            VarBinding::new(
                "wb".to_string(),
                Term::fn_apply(model_get_fn_name(prefix, WBUFFER_PREFIX), vec![st.clone()]),
            ),
            VarBinding::new(
                "new_wb".to_string(),
                smt2::seq::empty(types::wbuffer(prefix)),
            ),
        ],
        smt2::seq::foldl(
            Term::lambda(
                vec![
                    SortedVar::new("model".to_string(), types::model(prefix)),
                    SortedVar::new("entry".to_string(), types::wbuffer_entry(prefix)),
                ],
                Term::fn_apply(
                    format!("{prefix}.{MODEL_PREFIX}.{WBUFFER_PREFIX}.applyentryaction!"),
                    vec![
                        Term::ident("model".to_string()),
                        Term::ident("entry".to_string()),
                    ],
                ),
            ),
            Term::fn_apply(
                model_set_fn_name(prefix, WBUFFER_PREFIX),
                vec![st, Term::ident("new_wb".to_string())],
            ),
            Term::ident("wb".to_string()),
        ),
    );

    f.add_body(body);
    smt.function(f);
}

fn add_actions(smt: &mut Smt2Context, prefix: &str, iface: &VelosiAstInterface, mem_model: bool) {
    smt.section(String::from("Actions"));
    for f in iface.fields() {
        let fieldname = f.ident();
        smt.subsection(format!("interface field: {fieldname}"));

        if matches!(f.as_ref(), VelosiAstInterfaceField::Instruction(_)) {
            add_field_action(
                smt,
                prefix,
                f.write_actions_as_ref(),
                IFACE_PREFIX,
                fieldname,
                "exec",
                0,
            );
        }

        if mem_model {
            let store_action = VelosiAstInterfaceAction::new(
                Rc::new(VelosiAstExpr::IdentLiteral(
                    VelosiAstIdentLiteralExpr::with_name(
                        format!("{LOCAL_VARS_PREFIX}.{fieldname}"),
                        VelosiAstTypeInfo::Integer,
                    ),
                )),
                Rc::new(VelosiAstExpr::IdentLiteral(
                    VelosiAstIdentLiteralExpr::with_name(
                        format!("{WBUFFER_PREFIX}.{fieldname}"),
                        VelosiAstTypeInfo::Integer,
                    ),
                )),
                Default::default(),
            );
            add_field_action(
                smt,
                prefix,
                &[store_action],
                LOCAL_VARS_PREFIX,
                f.ident(),
                "store",
                f.size() * 8,
            );
        }

        add_field_action(
            smt,
            prefix,
            f.write_actions_as_ref(),
            IFACE_PREFIX,
            fieldname,
            "write",
            f.size() * 8,
        );

        if mem_model {
            let update_local_vars_action = VelosiAstInterfaceAction::new(
                Rc::new(VelosiAstExpr::IdentLiteral(
                    VelosiAstIdentLiteralExpr::with_name(
                        format!("{IFACE_PREFIX}.{fieldname}"),
                        VelosiAstTypeInfo::Integer,
                    ),
                )),
                Rc::new(VelosiAstExpr::IdentLiteral(
                    VelosiAstIdentLiteralExpr::with_name(
                        format!("{LOCAL_VARS_PREFIX}.{fieldname}"),
                        VelosiAstTypeInfo::Integer,
                    ),
                )),
                Default::default(),
            );
            add_field_action(
                smt,
                prefix,
                &[f.read_actions_as_ref(), &[update_local_vars_action]].concat(),
                IFACE_PREFIX,
                fieldname,
                "read",
                f.size() * 8,
            );
        } else {
            add_field_action(
                smt,
                prefix,
                f.read_actions_as_ref(),
                IFACE_PREFIX,
                fieldname,
                "read",
                f.size() * 8,
            );
        }
    }

    if mem_model {
        add_apply_entry_action(smt, prefix, iface);
        add_flush_action(smt, prefix);
    }
}
