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
use crate::ast;
use crate::ast::{Action, AstNodeGeneric, Interface, State};
use smt2::{DataType, Expr, Function, LetBinding, Smt2File};

fn add_model(smt: &mut Smt2File) {
    smt.add_section(String::from("Model"));
    let mut dt = DataType::new(String::from("Model"), 0);
    dt.add_comment(format!("Model Definition"));
    dt.add_field(format!("Model.State"), format!("State_t"));
    dt.add_field(format!("Model.IFace"), format!("IFace_t"));
    smt.add_datatype(dt);
    smt.add_section(String::from("Model"));
}

fn add_model_field_accessor(smt: &mut Smt2File, ftype: &str, fieldname: &str) {
    let name = format!("Model.{}.{}.get", ftype, fieldname);
    let mut f = Function::new(name, format!("{}Field.{}_t", ftype, fieldname));
    f.add_arg(String::from("Model_t"));

    let arg = Expr::ident(String::from("x!0"));
    let st = Expr::fn_apply(format!("Model.{}.get", ftype), vec![arg]);
    let e = Expr::fn_apply(format!("{}.{}.get", ftype, fieldname), vec![st]);
    f.add_body(e);
    smt.add_function(f);

    let name = format!("Model.{}.{}.set", ftype, fieldname);
    let mut f = Function::new(name, String::from("Model_t"));
    f.add_arg(String::from("Model_t"));
    f.add_arg(format!("{}Field.{}_t", ftype, fieldname));

    let arg = Expr::ident(String::from("x!0"));
    let arg2 = Expr::ident(String::from("x!1"));

    let st = Expr::fn_apply(format!("Model.{}.get", ftype), vec![arg.clone()]);
    let st = Expr::fn_apply(format!("{}.{}.set", ftype, fieldname), vec![st, arg2]);
    let e = Expr::fn_apply(format!("Model.{}.set", ftype), vec![arg, st]);
    f.add_body(e);

    smt.add_function(f);
}

fn add_model_slice_accessor(smt: &mut Smt2File, ftype: &str, fieldname: &str, slice: &str) {
    let name = format!("Model.{}.{}.{}.get", ftype, fieldname, slice);
    let mut f = Function::new(name, String::from("Int"));
    f.add_arg(String::from("Model_t"));

    let arg = Expr::ident(String::from("x!0"));
    let st = Expr::fn_apply(format!("Model.{}.get", ftype), vec![arg]);
    let e = Expr::fn_apply(format!("{}.{}.{}.get", ftype, fieldname, slice), vec![st]);
    f.add_body(e);

    smt.add_function(f);

    let name = format!("Model.{}.{}.{}.set", ftype, fieldname, slice);
    let mut f = Function::new(name, String::from("Model_t"));
    f.add_arg(String::from("Model_t"));
    f.add_arg(String::from("Int"));

    let arg = Expr::ident(String::from("x!0"));
    let arg2 = Expr::ident(String::from("x!1"));

    let st = Expr::fn_apply(format!("Model.{}.get", ftype), vec![arg.clone()]);

    // get the state

    // the field update (State.pte_t Int) State.pte_t)
    let st = Expr::fn_apply(
        format!("{}.{}.{}.set", ftype, fieldname, slice),
        vec![st, arg2],
    );

    let e = Expr::fn_apply(format!("Model.{}.set", ftype), vec![arg, st]);
    f.add_body(e);

    smt.add_function(f);
}

fn add_model_state_accessors(smt: &mut Smt2File, state: &State) {
    smt.add_section(String::from("Model State Accessors"));
    for f in state.fields() {
        smt.add_subsection(format!("state field: {}", f.name));
        add_model_field_accessor(smt, "State", &f.name);

        for b in &f.layout {
            add_model_slice_accessor(smt, "State", &f.name, &b.name);
        }
    }
}

fn add_model_iface_accessors(smt: &mut Smt2File, iface: &Interface) {
    smt.add_section(String::from("Model Interface Accessors"));

    for f in iface.fields() {
        smt.add_subsection(format!("interface field: {}", f.field.name));

        add_model_field_accessor(smt, "IFace", &f.field.name);
        for b in &f.field.layout {
            add_model_slice_accessor(smt, "IFace", &f.field.name, &b.name);
        }
    }
}

fn add_field_action(
    smt: &mut Smt2File,
    action: &Action,
    fieldname: &str,
    ty: &str,
    fieldwidth: u8,
) {
    let name = format!("Model.IFace.{}.{}action", fieldname, ty);
    let mut f = Function::new(name, String::from("Model_t"));
    f.add_arg(String::from("Model_t"));
    f.add_comment(format!("performs the write actions of {}", fieldname));

    let mut defs = Vec::new();

    let mut stvar = String::from("x!0");
    let mut newvar = String::from("st_1");

    // body = Expr::letexpr(vec![LetBinding::new(newvar.clone(), f)], Expr::ident(stvar));

    for (i, a) in action.action_components.iter().enumerate() {
        newvar = format!("st_{}", i + 1);

        let dst = match &a.dst {
            ast::Expr::Identifier { path, .. } => {
                if path.len() == 2 {
                    format!("Model.{}.{}.set", p2p(&path[0]), path[1])
                } else if path.len() == 3 {
                    format!("Model.{}.{}.{}.set", p2p(&path[0]), path[1], path[2])
                } else {
                    panic!("unexpected identifier lenght");
                }
            }
            _ => panic!("should not happen here! {}", &a.dst),
        };

        let src = expr_to_smt2(&a.src, &stvar);

        let fcall = Expr::fn_apply(dst, vec![Expr::ident(stvar.clone()), src]);

        defs.push(LetBinding::new(newvar.clone(), fcall));
        stvar = newvar;
    }

    let body = defs.iter().rev().fold(Expr::ident(stvar), |acc, x| {
        Expr::letexpr(vec![x.clone()], acc)
    });

    f.add_body(body);
    smt.add_function(f);
}

fn add_actions(smt: &mut Smt2File, iface: &Interface) {
    smt.add_section(String::from("Actions"));
    for f in iface.fields() {
        smt.add_subsection(format!("interface field: {}", f.field.name));

        // write actions
        if let Some(act) = &f.writeaction {
            add_field_action(smt, act, &f.field.name, "write", f.field.length as u8 * 8);
        }

        // read actions
        if let Some(act) = &f.readaction {
            add_field_action(smt, act, &f.field.name, "read", f.field.length as u8 * 8);
        }
    }
}

pub fn add_model_def(smt: &mut Smt2File, state: &State, iface: &Interface) {
    add_model(smt);
    add_model_state_accessors(smt, state);
    add_model_iface_accessors(smt, iface);
    add_actions(smt, iface)
}
