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
    VelosiAstExpr, VelosiAstInterface, VelosiAstInterfaceAction, VelosiAstMethod, VelosiAstState,
    VelosiAstTypeInfo, VelosiAstUnitSegment,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Constants
////////////////////////////////////////////////////////////////////////////////////////////////////

pub const IFACE_PREFIX: &str = "IFace";
pub const STATE_PREFIX: &str = "State";
pub const MODEL_PREFIX: &str = "Model";

////////////////////////////////////////////////////////////////////////////////////////////////////
// Model
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Adds the model definition to the context
pub fn add_model_def(smt: &mut Smt2Context, unit: &VelosiAstUnitSegment) {
    add_model(smt);
    add_model_state_accessors(smt, &unit.state);
    add_model_iface_accessors(smt, &unit.interface);
    add_actions(smt, &unit.interface)
}

fn add_model(smt: &mut Smt2Context) {
    smt.section(String::from("Model"));
    let mut dt = DataType::new(MODEL_PREFIX.to_string(), 0);
    dt.add_comment("Model Definition".to_string());
    dt.add_field(format!("{}.{}", MODEL_PREFIX, STATE_PREFIX), types::state());
    dt.add_field(format!("{}.{}", MODEL_PREFIX, IFACE_PREFIX), types::iface());

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
    format!("Model.{}.{}.{}.get!", ctxt, field, slice)
}

pub fn model_slice_set_fn_name(ctxt: &str, field: &str, slice: &str) -> String {
    let slice = slice.split('.').last().unwrap();
    let field = field.split('.').last().unwrap();
    format!("Model.{}.{}.{}.set!", ctxt, field, slice)
}

pub fn model_field_get_fn_name(ctxt: &str, field: &str) -> String {
    let field = field.split('.').last().unwrap();
    format!("Model.{}.{}.get!", ctxt, field)
}

pub fn model_field_set_fn_name(ctxt: &str, field: &str) -> String {
    let field = field.split('.').last().unwrap();
    format!("Model.{}.{}.set!", ctxt, field)
}

pub fn model_get_fn_name(ctxt: &str) -> String {
    format!("Model.{}.get!", ctxt)
}

pub fn model_set_fn_name(ctxt: &str) -> String {
    format!("Model.{}.set!", ctxt)
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

fn add_model_state_accessors(smt: &mut Smt2Context, state: &VelosiAstState) {
    smt.section(String::from("Model State Accessors"));
    for f in state.fields() {
        smt.subsection(format!("state field: {}", f.ident_as_str()));
        add_model_field_accessor(smt, STATE_PREFIX, f.ident_as_str());

        for s in f.layout_as_slice() {
            add_model_slice_accessor(smt, STATE_PREFIX, f.ident_as_str(), s.ident_as_str());
        }
    }
}

fn add_model_iface_accessors(smt: &mut Smt2Context, iface: &VelosiAstInterface) {
    smt.section(String::from("Model Interface Accessors"));

    for f in iface.fields() {
        smt.subsection(format!("interface field: {}", f.ident_as_str()));
        add_model_field_accessor(smt, IFACE_PREFIX, f.ident_as_str());
        for s in f.layout_as_slice() {
            add_model_slice_accessor(smt, IFACE_PREFIX, f.ident_as_str(), s.ident_as_str());
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Actions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn action_fn_name(fieldname: &str, ty: &str) -> String {
    let fieldname = fieldname.split('.').last().unwrap();
    format!(
        "{}.{}.{}.{}action!",
        MODEL_PREFIX, IFACE_PREFIX, fieldname, ty
    )
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
    f.add_comment(format!("performs the write actions of {}", fieldname));

    let mut defs = Vec::new();
    let mut stvar = String::from("st");

    // body = Term::letexpr(vec![VarBinding::new(newvar.clone(), f)], Term::ident(stvar));

    for (i, a) in actions.iter().enumerate() {
        let newvar = format!("st_{}", i + 1);

        let dst = match &a.dst {
            VelosiAstExpr::IdentLiteral(i) => {
                if i.path.len() == 2 {
                    // if we have flags, then this is bascially a field access
                    model_field_set_fn_name(p2p(i.path[0].as_str()), i.path[1].as_str())
                } else if i.path.len() == 3 {
                    model_slice_set_fn_name(
                        p2p(i.path[0].as_str()),
                        i.path[1].as_str(),
                        i.path[2].as_str(),
                    )
                } else {
                    unreachable!("path of unexpected length: {:?}", i.path);
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

fn add_actions(smt: &mut Smt2Context, iface: &VelosiAstInterface) {
    smt.section(String::from("Actions"));
    for f in iface.fields() {
        smt.subsection(format!("interface field: {}", f.ident_as_str()));

        add_field_action(
            smt,
            f.write_actions_as_ref(),
            f.ident_as_str(),
            "write",
            f.size() * 8,
        );
        add_field_action(
            smt,
            f.read_actions_as_ref(),
            f.ident_as_str(),
            "read",
            f.size() * 8,
        );
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Assumptins
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_fn_arg_assms(m: &VelosiAstMethod, inbitwidth: u64, outbitwidth: u64) -> Vec<Term> {
    let mut conds = Vec::new();

    // the minimum bitwidth of the unit
    let minbits = std::cmp::min(inbitwidth, outbitwidth);
    let maxbits = std::cmp::max(inbitwidth, outbitwidth);

    // that's a bit hacky: it assumes that there is only one size parameter
    let mut szarg = String::new();
    for a in m.params.iter() {
        if matches!(a.ptype.typeinfo, VelosiAstTypeInfo::Size) {
            szarg = a.ident_to_string();
        }
    }

    // the following requires on a specific
    for a in m.params.iter() {
        match a.ptype.typeinfo {
            VelosiAstTypeInfo::Integer => {
                let maxsize = if maxbits < 64 {
                    (1u64 << maxbits) - 1
                } else {
                    0xffff_ffff_ffff_ffff
                };
                conds.push(Term::bvge(Term::ident(a.ident_to_string()), Term::num(0)));
                conds.push(Term::bvle(
                    Term::ident(a.ident_to_string()),
                    Term::num(maxsize),
                ));
            }
            VelosiAstTypeInfo::Bool => {
                conds.push(Term::lor(
                    Term::bveq(Term::ident(a.ident_to_string()), Term::num(0)),
                    Term::bveq(Term::ident(a.ident_to_string()), Term::num(1)),
                ));
            }
            VelosiAstTypeInfo::GenAddr => {
                // should be the paddr position
                let maxpaddr = if maxbits < 64 {
                    (1u64 << maxbits) - 1
                } else {
                    0xffff_ffff_ffff_ffff
                };
                // should be the paddr position: va <= 0 <= MAX_VADDR
                conds.push(Term::bvge(Term::ident(a.ident_to_string()), Term::num(0)));
                conds.push(Term::bvle(
                    Term::ident(a.ident_to_string()),
                    Term::num(maxpaddr),
                ));

                // overflow: va + sz <= MAX_ADDR  ==> va <= MAX_ADDR - sz
                conds.push(Term::bvle(
                    Term::ident(a.ident_to_string()),
                    Term::bvsub(Term::num(maxpaddr), Term::ident(szarg.clone())),
                ));
            }
            VelosiAstTypeInfo::VirtAddr => {
                let maxvaddr = if inbitwidth < 64 {
                    (1u64 << inbitwidth) - 1
                } else {
                    0xffff_ffff_ffff_ffff
                };
                // should be the vaddr position: va <= 0 <= MAX_VADDR
                conds.push(Term::bvge(Term::ident(a.ident_to_string()), Term::num(0)));
                conds.push(Term::bvle(
                    Term::ident(a.ident_to_string()),
                    Term::num(maxvaddr),
                ));

                // overflow: va + sz <= MAX_VADDR  ==> va <= MAX_VADDR - sz
                conds.push(Term::bvle(
                    Term::ident(a.ident_to_string()),
                    Term::bvsub(Term::num(maxvaddr), Term::ident(szarg.clone())),
                ));
            }
            VelosiAstTypeInfo::PhysAddr => {
                // should be the paddr position
                let maxpaddr = if outbitwidth < 64 {
                    (1u64 << outbitwidth) - 1
                } else {
                    0xffff_ffff_ffff_ffff
                };
                // should be the paddr position: va <= 0 <= MAX_VADDR
                conds.push(Term::bvge(Term::ident(a.ident_to_string()), Term::num(0)));
                conds.push(Term::bvle(
                    Term::ident(a.ident_to_string()),
                    Term::num(maxpaddr),
                ));

                // overflow: va + sz <= MAX_PADDR  ==> va <= MAX_PADDR - sz
                conds.push(Term::bvle(
                    Term::ident(a.ident_to_string()),
                    Term::bvsub(Term::num(maxpaddr), Term::ident(szarg.clone())),
                ));
            }
            VelosiAstTypeInfo::Size => {
                let maxsize = if minbits < 64 {
                    (1u64 << minbits) - 1
                } else {
                    0xffff_ffff_ffff_ffff
                };
                conds.push(Term::bvge(Term::ident(a.ident_to_string()), Term::num(0)));
                conds.push(Term::bvle(
                    Term::ident(a.ident_to_string()),
                    Term::num(maxsize),
                ));
            }
            VelosiAstTypeInfo::TypeRef(_) => {}
            VelosiAstTypeInfo::Flags => { /* nothing to do with flags */ }
            _ => unreachable!("unsuppored type"),
        }
    }

    conds
}

fn add_assms(smt: &mut Smt2Context, unit: &VelosiAstUnitSegment) {
    smt.section(String::from("Assumptions"));

    let fun = unit.get_method("map").unwrap();

    let mut f = Function::new(String::from("map.assms"), types::boolean());

    f.add_arg(String::from("st"), types::model());
    for p in fun.params.iter() {
        f.add_arg(p.ident_to_string(), types::type_to_smt2(&p.ptype));
    }

    let mut conds = add_fn_arg_assms(fun, unit.inbitwidth, unit.outbitwidth);
    for c in &fun.requires {
        conds.push(expr_to_smt2(c, "st"));
    }

    let body = conds.drain(..).fold(Term::binary(true), Term::land);
    f.add_body(body);

    smt.function(f);
}
