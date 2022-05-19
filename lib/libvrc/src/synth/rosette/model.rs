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
use rosettelang::{FunctionDef, RExpr, RosetteFile, StructDef};

// crate imports
use super::expr;
use crate::ast::{Action, BinOp, Expr, Interface, Method, State};

const MODEL: &str = "model";

fn add_model(rkt: &mut RosetteFile) {
    rkt.add_section(String::from("Model Defintions"));

    let attrib = String::from("#:transparent");
    let mut s = StructDef::new(
        String::from(MODEL),
        vec![String::from("st"), String::from("var")],
        attrib,
    );
    s.add_doc(String::from(
        "Model Definition: Combines State and Interface",
    ));
    rkt.add_struct_def(s);

    // add the constructor
    let body = RExpr::fncall(
        String::from(MODEL),
        vec![
            RExpr::fncall(String::from("make-state-fields"), vec![]),
            RExpr::fncall(String::from("make-iface-fields"), vec![]),
        ],
    );
    let mut f = FunctionDef::new(String::from("make-model"), Vec::new(), vec![body]);
    f.add_comment(String::from("State Constructor"));
    rkt.add_function_def(f);

    rkt.add_section(String::from("Model Accessors"));

    let statevar = String::from("mst");
    let valvar = String::from("newst");

    // get state from the model

    let fnname = String::from("model-get-state");
    let fnargs = vec![statevar.clone()];
    let fnbody = RExpr::matchexpr(
        statevar.clone(),
        vec![
            (
                RExpr::fncall(
                    String::from(MODEL),
                    vec![RExpr::var(String::from("s")), RExpr::var(String::from("i"))],
                ),
                vec![RExpr::var(String::from("s"))],
            ),
            (
                RExpr::var(String::from("_")),
                vec![
                    RExpr::fncall(
                        String::from("printf"),
                        vec![RExpr::text(String::from("wrong state supplied"))],
                    ),
                    RExpr::var(statevar.clone()),
                ],
            ),
        ],
    );
    let mut f = FunctionDef::new(fnname, fnargs, vec![fnbody]);
    f.add_comment(String::from("Obtains the unit's state from the model"));
    rkt.add_function_def(f);

    // set the state of the model

    let fnname = String::from("model-set-state");
    let fnargs = vec![statevar.clone(), valvar.clone()];
    let fnbody = RExpr::fncall(
        String::from("struct-copy"),
        vec![
            RExpr::var(String::from(MODEL)),
            RExpr::var(statevar.clone()),
            RExpr::block(vec![(String::from("st"), RExpr::var(valvar.clone()))]),
        ],
    );
    let mut f = FunctionDef::new(fnname, fnargs, vec![fnbody]);
    f.add_comment(String::from("Updates the unit's state in the model"));
    rkt.add_function_def(f);

    // get the interface state

    let fnname = String::from("model-get-interface");
    let fnargs = vec![statevar.clone()];
    let fnbody = RExpr::matchexpr(
        statevar.clone(),
        vec![
            (
                RExpr::fncall(
                    String::from(MODEL),
                    vec![RExpr::var(String::from("s")), RExpr::var(String::from("i"))],
                ),
                vec![RExpr::var(String::from("i"))],
            ),
            (
                RExpr::var(String::from("_")),
                vec![
                    RExpr::fncall(
                        String::from("printf"),
                        vec![RExpr::text(String::from("wrong state supplied"))],
                    ),
                    RExpr::var(statevar.clone()),
                ],
            ),
        ],
    );
    let mut f = FunctionDef::new(fnname, fnargs, vec![fnbody]);
    f.add_comment(String::from(
        "Obtains the interface variables from the model",
    ));
    rkt.add_function_def(f);

    // set the interface state

    let fnname = String::from("model-set-interface");
    let fnargs = vec![statevar.clone(), valvar.clone()];
    let fnbody = RExpr::fncall(
        String::from("struct-copy"),
        vec![
            RExpr::var(String::from(MODEL)),
            RExpr::var(statevar),
            RExpr::block(vec![(String::from("var"), RExpr::var(valvar))]),
        ],
    );
    let mut f = FunctionDef::new(fnname, fnargs, vec![fnbody]);
    f.add_comment(String::from("Updates interface variables of the model"));
    rkt.add_function_def(f);
}

fn add_model_field_accessor(rkt: &mut RosetteFile, ftype: &str, fieldname: &str) {
    let stvar = String::from("st");
    let valvar = String::from("val");

    // load function

    let fname = format!("{}-load-{}", ftype, fieldname);
    let args = vec![stvar.clone()];
    let body = RExpr::fncall(
        format!("{}-fields-load-{}", ftype, fieldname),
        vec![RExpr::fncall(
            format!("model-get-{}", ftype),
            vec![RExpr::var(stvar.clone())],
        )],
    );
    let mut fdef = FunctionDef::new(fname, args, vec![body]);
    fdef.add_comment(format!(
        "loads the {} field from the {} of the model",
        fieldname, ftype
    ));
    rkt.add_function_def(fdef);

    // store function

    let fname = format!("{}-store-{}", ftype, fieldname);
    let args = vec![stvar.clone(), valvar.clone()];
    let body = RExpr::fncall(
        format!("model-set-{}", ftype),
        vec![
            RExpr::var(stvar.clone()),
            RExpr::fncall(
                format!("{}-fields-store-{}", ftype, fieldname),
                vec![
                    RExpr::fncall(format!("model-get-{}", ftype), vec![RExpr::var(stvar)]),
                    RExpr::var(valvar),
                ],
            ),
        ],
    );
    let mut fdef = FunctionDef::new(fname, args, vec![body]);
    fdef.add_comment(format!(
        "stores the {} field into the {} of the model",
        fieldname, ftype
    ));
    rkt.add_function_def(fdef);
}

fn add_model_slice_accessor(rkt: &mut RosetteFile, ftype: &str, fieldname: &str, slice: &str) {
    let stvar = String::from("st");
    let valvar = String::from("val");

    // load function

    let fname = format!("{}-{}-{}-read", ftype, fieldname, slice);
    let args = vec![stvar.clone()];
    let body = RExpr::fncall(
        format!("{}-fields-{}-{}-read", ftype, fieldname, slice),
        vec![RExpr::fncall(
            format!("model-get-{}", ftype),
            vec![RExpr::var(stvar.clone())],
        )],
    );
    let mut fdef = FunctionDef::new(fname, args, vec![body]);
    fdef.add_comment(format!(
        "loads the {}.{} field from the {} of the model",
        fieldname, slice, ftype
    ));
    rkt.add_function_def(fdef);

    // store function

    let fname = format!("{}-{}-{}-write", ftype, fieldname, slice);
    let args = vec![stvar.clone(), valvar.clone()];
    let body = RExpr::fncall(
        format!("model-set-{}", ftype),
        vec![
            RExpr::var(stvar.clone()),
            RExpr::fncall(
                format!("{}-fields-{}-{}-write", ftype, fieldname, slice),
                vec![
                    RExpr::fncall(format!("model-get-{}", ftype), vec![RExpr::var(stvar)]),
                    RExpr::var(valvar),
                ],
            ),
        ],
    );
    let mut fdef = FunctionDef::new(fname, args, vec![body]);
    fdef.add_comment(format!(
        "stores the {}.{} field from the {} of the model",
        fieldname, slice, ftype
    ));
    rkt.add_function_def(fdef);
}

fn add_model_state_accessors(rkt: &mut RosetteFile, state: &State) {
    rkt.add_section(String::from("Model State Accessors"));

    for f in state.fields() {
        rkt.add_subsection(format!("state field: {}", f.name));

        add_model_field_accessor(rkt, "state", &f.name);

        for b in &f.layout {
            add_model_slice_accessor(rkt, "state", &f.name, &b.name);
        }
    }
}

fn add_model_iface_accessors(rkt: &mut RosetteFile, iface: &Interface) {
    rkt.add_section(String::from("Model Interface Accessors"));

    for f in iface.fields() {
        rkt.add_subsection(format!("interface field: {}", f.field.name));

        add_model_field_accessor(rkt, "interface", &f.field.name);

        for b in &f.field.layout {
            add_model_slice_accessor(rkt, "interface", &f.field.name, &b.name);
        }
    }
}

fn field_read_access_expr(e: &Expr, fieldwidth: u8, stvar: &str) -> RExpr {
    match e {
        Expr::Identifier { path, .. } => {
            if path.len() == 2 {
                let ident = format!("{}-load-{}", path[0], path[1]);
                RExpr::fncall(ident, vec![RExpr::var(stvar.to_string())])
            } else if path.len() == 3 {
                let ident = format!("{}-{}-{}-read", path[0], path[1], path[2]);
                RExpr::fncall(ident, vec![RExpr::var(stvar.to_string())])
            } else {
                panic!("unexpected identifier lenght");
            }
        }
        Expr::Number { value, .. } => RExpr::num(fieldwidth, *value),
        Expr::Boolean { value: true, .. } => RExpr::num(fieldwidth, 1),
        Expr::Boolean { value: false, .. } => RExpr::num(fieldwidth, 0),
        Expr::BinaryOperation { op, lhs, rhs, .. } => match op {
            BinOp::RShift => RExpr::bvshr(
                field_read_access_expr(lhs, fieldwidth, stvar),
                field_read_access_expr(rhs, fieldwidth, stvar),
            ),
            BinOp::LShift => RExpr::bvshl(
                field_read_access_expr(lhs, fieldwidth, stvar),
                field_read_access_expr(rhs, fieldwidth, stvar),
            ),
            a => RExpr::var(format!("UNKNOWN: {:?}", a)),
        },
        a => RExpr::var(format!("UNKNOWN: {:?}", a)),
    }
}

fn add_field_action(
    rkt: &mut RosetteFile,
    action: &Action,
    fieldname: &str,
    ty: &str,
    fieldwidth: u8,
) {
    let fname = format!("interface-{}-{}-action", fieldname, ty);
    let stvar = String::from("st");
    let args = vec![stvar];

    let mut defs = Vec::new();
    let mut stvar = String::from("st");
    let mut newvar = String::from("st_1");
    for (i, a) in action.action_components.iter().enumerate() {
        newvar = format!("st_{}", i + 1);

        let dst = match &a.dst {
            Expr::Identifier { path, .. } => {
                if path.len() == 2 {
                    format!("{}-store-{}", path[0], path[1])
                } else if path.len() == 3 {
                    format!("{}-{}-{}-write", path[0], path[1], path[2])
                } else {
                    panic!("unexpected identifier lenght");
                }
            }
            _ => String::from("UNKNOWN1"),
        };

        let src = field_read_access_expr(&a.src, fieldwidth, &stvar);

        defs.push((
            newvar.clone(),
            RExpr::fncall(dst, vec![RExpr::var(stvar), src]),
        ));
        stvar = newvar.clone();
    }

    let lets = RExpr::var(newvar);
    let body = RExpr::letstart(defs, vec![lets]);

    let mut fdef = FunctionDef::new(fname, args, vec![body]);
    fdef.add_comment(format!("performs the write actions of {}", fieldname));
    rkt.add_function_def(fdef);
}

fn add_actions(rkt: &mut RosetteFile, iface: &Interface) {
    rkt.add_section(String::from("Actions"));
    for f in iface.fields() {
        rkt.add_subsection(format!("interface field: {}", f.field.name));

        // write actions

        if let Some(action) = &f.writeaction {
            add_field_action(
                rkt,
                action,
                &f.field.name,
                "write",
                f.field.length as u8 * 8,
            );
        }

        // read actions

        // TODO: fill in body
        if let Some(action) = &f.readaction {
            add_field_action(rkt, action, &f.field.name, "read", f.field.length as u8 * 8);
        }
    }
}

pub fn add_translate(rkt: &mut RosetteFile, translate: &Method) {
    rkt.add_section(String::from("Translation Function"));

    // let's add the arguments
    let mut args = vec![String::from("st")];
    for a in translate.args.iter() {
        args.push(a.name.clone());
    }

    // add the requires as assert
    let mut body = Vec::new();
    for p in translate.requires.iter() {
        body.push(RExpr::assert(expr::expr_to_rosette(p)));
    }

    // convert statements into rosette statements
    if let Some(stmts) = &translate.stmts {
        body.push(expr::stmt_to_rosette(stmts))
    }

    rkt.add_new_function_def(String::from("translate"), args, body)
}

pub fn add_matchflags(rkt: &mut RosetteFile, matchflags: &Method) {
    rkt.add_section(String::from("Matchflags Function"));

    // let's add the arguments
    let mut args = vec![String::from("st")];
    for a in matchflags.args.iter() {
        args.push(a.name.clone());
    }

    // add the requires as assert
    let mut body = Vec::new();
    for p in matchflags.requires.iter() {
        body.push(RExpr::assert(expr::expr_to_rosette(p)));
    }

    // convert statements into rosette statements
    if let Some(stmts) = &matchflags.stmts {
        body.push(expr::stmt_to_rosette(stmts))
    }

    rkt.add_new_function_def(String::from("matchflags"), args, body)
}

pub fn add_model_def(rkt: &mut RosetteFile, state: &State, iface: &Interface) {
    add_model(rkt);
    add_model_state_accessors(rkt, state);
    add_model_iface_accessors(rkt, iface);
    add_actions(rkt, iface);
}
