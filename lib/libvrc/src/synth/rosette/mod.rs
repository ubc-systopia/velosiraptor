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

//! Synthesis Module: Rosette

// external libraries
use std::fs;
use std::path::{Path, PathBuf};

// the used libraries
use crate::ast::{Action, AstRoot, BitSlice, Expr, Interface, Method, State, Type};
use crate::synth::SynthError;
use rosettelang::{FunctionDef, RExpr, RosetteFile, StructDef, VarDef};

mod expr;

pub struct SynthRosette {
    outdir: PathBuf,
    pkg: String,
}

const STATEFIELDS: &str = "statefields";
const IFACEFIELDS: &str = "ifacefields";
const MODEL: &str = "model";

impl SynthRosette {
    pub fn new(outdir: &Path, pkg: String) -> Self {
        SynthRosette {
            outdir: outdir.join(&pkg).join("synth"),
            pkg,
        }
    }

    fn add_bitvector_defs(rkt: &mut RosetteFile) {
        for x in [64, 32, 16, 8] {
            let ident = format!("int{}?", x);
            let arg = format!("{}", x);
            rkt.add_new_var(
                ident,
                RExpr::fncall(String::from("bitvector"), vec![RExpr::var(arg)]),
            );
        }

        for x in [64, 32, 16, 8] {
            let ident = format!("int{}", x);
            let arg = String::from("i");
            let arg2 = format!("int{}?", x);
            rkt.add_new_function_def(
                ident,
                vec![arg.clone()],
                vec![RExpr::fncall(
                    String::from("bv"),
                    vec![RExpr::var(arg), RExpr::var(arg2)],
                )],
            );
        }
    }

    fn add_requires(rkt: &mut RosetteFile) {
        rkt.add_new_require(String::from("rosette/lib/synthax"));
        rkt.add_new_require(String::from("rosette/lib/destruct"));
    }

    fn add_insert_extract(
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
                RExpr::var(oldname.clone()),
                // shift the mask to the start of the slice
                RExpr::num(fieldsize, !(mask << bslice.start)),
            ),
            // new value
            RExpr::bvshl(
                RExpr::bvand(RExpr::var(varname.clone()), RExpr::num(fieldsize, mask)),
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

    fn add_read_write_slice(rkt: &mut RosetteFile, ftype: &str, field: &str, bslice: &str) {
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
                            vec![RExpr::var(stname.clone())],
                        ),
                        RExpr::var(varname.clone()),
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

    fn add_state_fields(rkt: &mut RosetteFile, state: &State) {
        rkt.add_section(String::from("State Fields"));
        let statevar = String::from("st");
        let valvar = String::from("val");
        // the state struct
        let entries = state
            .fields()
            .iter()
            .map(|f| f.name.clone())
            .collect::<Vec<String>>();
        let attrib = String::from("#:transparent");
        let mut s = StructDef::new(String::from(STATEFIELDS), entries, attrib);
        s.add_doc(String::from(
            "State Definition - contains all fiends in the state spec",
        ));
        rkt.add_struct_def(s);

        // add the constructor
        let body = RExpr::fncall(
            String::from(STATEFIELDS),
            state
                .fields()
                .iter()
                .map(|f| RExpr::num((f.length * 8) as u8, 0))
                .collect::<Vec<RExpr>>(),
        );
        let mut f = FunctionDef::new(String::from("make-state-fields"), Vec::new(), vec![body]);
        f.add_comment(String::from("State Constructor"));
        rkt.add_function_def(f);

        for f in state.fields() {
            rkt.add_subsection(format!("State Field: '{}'", f.name));

            let fname = format!("state-fields-load-{}", f.name);
            let args = vec![statevar.clone()];

            let sfields = state
                .fields()
                .iter()
                .map(|e| RExpr::var(e.name.clone()))
                .collect::<Vec<RExpr>>();
            let body = RExpr::matchexpr(
                statevar.clone(),
                vec![
                    (
                        RExpr::fncall(String::from(STATEFIELDS), sfields),
                        vec![RExpr::var(f.name.clone())],
                    ),
                    (
                        RExpr::var(String::from("_")),
                        vec![
                            RExpr::fncall(
                                String::from("printf"),
                                vec![RExpr::text(String::from("wrong state supplied"))],
                            ),
                            RExpr::var(String::from("st")),
                        ],
                    ),
                ],
            );
            let mut fdef = FunctionDef::new(fname, args, vec![body]);
            fdef.add_comment(String::from("Field accessor"));
            rkt.add_function_def(fdef);

            let fname = format!("state-fields-store-{}", f.name);
            let args = vec![statevar.clone(), valvar.clone()];
            let body = RExpr::fncall(
                String::from("struct-copy"),
                vec![
                    RExpr::var(String::from(STATEFIELDS)),
                    RExpr::var(statevar.clone()),
                    RExpr::block(vec![(f.name.clone(), RExpr::var(valvar.clone()))]),
                ],
            );
            let mut fdef = FunctionDef::new(fname, args, vec![body]);
            fdef.add_comment(String::from("Field update"));
            rkt.add_function_def(fdef);

            for b in &f.layout {
                rkt.add_subsection(format!("BitSlice: '{}.{}'", f.name, b.name));
                SynthRosette::add_insert_extract(rkt, "state", &f.name, f.length, b);
                SynthRosette::add_read_write_slice(rkt, "state", &f.name, &b.name)
            }
        }
    }

    fn add_interface_fields(rkt: &mut RosetteFile, iface: &Interface) {
        rkt.add_section(String::from("Interface Fields"));

        let statevar = String::from("st");
        let valvar = String::from("val");

        // the state struct
        let entries = iface
            .fields()
            .iter()
            .map(|f| f.field.name.clone())
            .collect::<Vec<String>>();
        let attrib = String::from("#:transparent");
        let mut s = StructDef::new(String::from(IFACEFIELDS), entries, attrib);
        s.add_doc(String::from(
            "Interface Definition - contains all fiends in the state spec",
        ));

        // add the constructor
        rkt.add_struct_def(s);

        let body = RExpr::fncall(
            String::from(IFACEFIELDS),
            iface
                .fields()
                .iter()
                .map(|f| RExpr::num((f.field.length * 8) as u8, 0))
                .collect::<Vec<RExpr>>(),
        );
        let mut f = FunctionDef::new(String::from("make-iface-fields"), Vec::new(), vec![body]);
        f.add_comment(String::from("Interface Constructor"));
        rkt.add_function_def(f);

        for f in iface.fields() {
            rkt.add_subsection(format!("Interface Field: '{}'", f.field.name));

            let fname = format!("interface-fields-load-{}", f.field.name);
            let args = vec![statevar.clone()];
            let sfields = iface
                .fields()
                .iter()
                .map(|e| RExpr::var(e.field.name.clone()))
                .collect::<Vec<RExpr>>();
            let body = RExpr::matchexpr(
                statevar.clone(),
                vec![
                    (
                        RExpr::fncall(String::from(IFACEFIELDS), sfields),
                        vec![RExpr::var(f.field.name.clone())],
                    ),
                    (
                        RExpr::var(String::from("_")),
                        vec![
                            RExpr::fncall(
                                String::from("printf"),
                                vec![RExpr::text(String::from("wrong state supplied"))],
                            ),
                            RExpr::var(String::from("st")),
                        ],
                    ),
                ],
            );
            let mut fdef = FunctionDef::new(fname, args, vec![body]);
            fdef.add_comment(String::from("Field accessor"));
            rkt.add_function_def(fdef);

            let fname = format!("interface-fields-store-{}", f.field.name);
            let args = vec![statevar.clone(), valvar.clone()];
            let body = RExpr::fncall(
                String::from("struct-copy"),
                vec![
                    RExpr::var(String::from(IFACEFIELDS)),
                    RExpr::var(statevar.clone()),
                    RExpr::block(vec![(f.field.name.clone(), RExpr::var(valvar.clone()))]),
                ],
            );
            let mut fdef = FunctionDef::new(fname, args, vec![body]);
            fdef.add_comment(String::from("Field update"));
            rkt.add_function_def(fdef);

            for b in &f.field.layout {
                rkt.add_subsection(format!("BitSlice: '{}.{}'", f.field.name, b.name));
                SynthRosette::add_insert_extract(
                    rkt,
                    "interface",
                    &f.field.name,
                    f.field.length,
                    b,
                );
                SynthRosette::add_read_write_slice(rkt, "interface", &f.field.name, &b.name)
            }
        }
    }

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
        let fnargs = vec![statevar.clone(), valvar.clone()];
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
                RExpr::var(statevar.clone()),
                RExpr::block(vec![(String::from("var"), RExpr::var(valvar.clone()))]),
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
                        RExpr::fncall(
                            format!("model-get-{}", ftype),
                            vec![RExpr::var(stvar.clone())],
                        ),
                        RExpr::var(valvar.clone()),
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
            format!("{}-fields-load-{}", ftype, fieldname),
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
                        RExpr::fncall(
                            format!("model-get-{}", ftype),
                            vec![RExpr::var(stvar.clone())],
                        ),
                        RExpr::var(valvar.clone()),
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

            SynthRosette::add_model_field_accessor(rkt, "state", &f.name);

            for b in &f.layout {
                SynthRosette::add_model_slice_accessor(rkt, "state", &f.name, &b.name);
            }
        }
    }

    fn add_model_iface_accessors(rkt: &mut RosetteFile, iface: &Interface) {
        rkt.add_section(String::from("Model Interface Accessors"));

        for f in iface.fields() {
            rkt.add_subsection(format!("interface field: {}", f.field.name));

            SynthRosette::add_model_field_accessor(rkt, "interface", &f.field.name);

            for b in &f.field.layout {
                SynthRosette::add_model_slice_accessor(rkt, "interface", &f.field.name, &b.name);
            }
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
        let args = vec![stvar.clone()];

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
                        format!("{}-{}-{}-write", path[0], path[1], path[0])
                    } else {
                        panic!("unexpected identifier lenght");
                    }
                }
                _ => String::from("UNKNOWN"),
            };

            let src = match &a.src {
                Expr::Identifier { path, .. } => {
                    if path.len() == 2 {
                        let ident = format!("{}-load-{}", path[0], path[1]);
                        RExpr::fncall(ident, vec![RExpr::var(stvar.clone())])
                    } else if path.len() == 3 {
                        let ident = format!("{}-{}-{}-read", path[0], path[1], path[0]);
                        RExpr::fncall(ident, vec![RExpr::var(stvar.clone())])
                    } else {
                        panic!("unexpected identifier lenght");
                    }
                }
                Expr::Number { value, .. } => RExpr::num(fieldwidth, *value),
                Expr::Boolean { value: true, .. } => RExpr::num(fieldwidth, 1),
                Expr::Boolean { value: false, .. } => RExpr::num(fieldwidth, 0),
                _ => RExpr::var(String::from("UNKNOWN")),
            };

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
                SynthRosette::add_field_action(
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
                SynthRosette::add_field_action(
                    rkt,
                    action,
                    &f.field.name,
                    "read",
                    f.field.length as u8 * 8,
                );
            }
        }
    }

    fn add_methods(rkt: &mut RosetteFile, methods: &[Method]) {
        rkt.add_section(String::from("Methods"));

        for m in methods {
            match m.name.as_str() {
                "translate" => continue,
                "map" => continue,
                "unmap" => continue,
                "protect" => continue,
                _ => (),
            }

            // let's add the arguments
            let mut args = vec![String::from("st")];
            for a in m.args.iter() {
                args.push(a.name.clone());
            }

            // add the requires as assert
            let mut body = Vec::new();
            for p in m.requires.iter() {
                body.push(RExpr::assert(expr::expr_to_rosette(p)));
            }

            // convert statements into rosette statements
            if let Some(stmts) = &m.stmts {
                body.push(expr::stmt_to_rosette(stmts))
            }

            rkt.add_new_function_def(m.name.clone(), args, body)
        }
    }

    fn add_translate(rkt: &mut RosetteFile, translate: &Method) {
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

    fn add_grammar(rkt: &mut RosetteFile, iface: &Interface) {
        rkt.add_section(String::from("Grammar Definition"));

        rkt.add_subsection(String::from("Sequencing"));
        // adding the struct definition
        rkt.add_new_struct_def(
            String::from("Seq"),
            vec![String::from("op"), String::from("rem")],
            String::from("#:transparent"),
        );
        rkt.add_new_struct_def(
            String::from("Return"),
            vec![],
            String::from("#:transparent"),
        );

        rkt.add_subsection(String::from("Grammar Elements"));

        for f in iface.fields() {
            for b in &f.field.layout {
                let arg = String::from("arg");
                let ident = format!("Op_Iface_{}_{}_Insert", f.field.name, b.name);
                rkt.add_new_struct_def(ident, vec![arg], String::from("#:transparent"));
            }
            let ident = format!("Op_Iface_{}_WriteAction", f.field.name);
            rkt.add_new_struct_def(ident, vec![], String::from("#:transparent"));
            let ident = format!("Op_Iface_{}_ReadAction", f.field.name);
            rkt.add_new_struct_def(ident, vec![], String::from("#:transparent"));
        }

        // now define the grammar
        let fname = String::from("ast-grammar");
        let args = vec![
            String::from("st"),
            String::from("va"),
            String::from("pa"),
            String::from("size"),
            String::from("flags"),
        ];
        let mut body = vec![RExpr::block(vec![(
            String::from("stmts"),
            RExpr::fncall(
                String::from("choose"),
                vec![
                    RExpr::fncall(String::from("Return"), vec![]),
                    RExpr::fncall(
                        String::from("Seq"),
                        vec![
                            RExpr::fncall(String::from("ops"), vec![]),
                            RExpr::fncall(String::from("stmts"), vec![]),
                        ],
                    ),
                ],
            ),
        )])];

        let mut ops = Vec::new();
        for f in iface.fields() {
            for b in &f.field.layout {
                // let arg = String::from("arg");
                let ident = format!("Op_Iface_{}_{}_Insert", f.field.name, b.name);
                let args = RExpr::fncall(String::from("valexpr"), vec![]);
                ops.push(RExpr::fncall(ident, vec![args]));
            }
            let ident = format!("Op_Iface_{}_WriteAction", f.field.name);
            ops.push(RExpr::fncall(ident, vec![]));
            let ident = format!("Op_Iface_{}_ReadAction", f.field.name);
            ops.push(RExpr::fncall(ident, vec![]));
        }
        body.push(RExpr::block(vec![(
            String::from("ops"),
            RExpr::fncall(String::from("choose"), ops),
        )]));

        body.push(RExpr::block(vec![(
            String::from("valexpr"),
            RExpr::fncall(
                String::from("choose"),
                vec![
                    RExpr::var(String::from("va")),
                    RExpr::var(String::from("pa")),
                    RExpr::var(String::from("size")),
                    RExpr::var(String::from("flags")),
                    RExpr::var(String::from("(?? int64)")),
                    RExpr::var(String::from("(?? int32)")),
                    RExpr::var(String::from("(?? int16)")),
                    RExpr::var(String::from("(?? int8)")),
                ],
            ),
        )]));

        let mut fdef = FunctionDef::new(fname, args, body);
        fdef.add_comment(String::from("defines the grammar for synthesis"));
        fdef.add_suffix(String::from("grammar"));
        rkt.add_function_def(fdef);
    }

    fn add_interp_function(rkt: &mut RosetteFile, iface: &Interface) {
        rkt.add_section(String::from("Interpretation Function"));

        let fname = String::from("ast-interpret");
        let args = vec![String::from("prog"), String::from("st")];

        let mut matches = vec![RExpr::var(String::from("s"))];
        for f in iface.fields() {
            for b in &f.field.layout {
                let structident = format!("(Op_Iface_{}_{}_Insert v)", f.field.name, b.name);
                let fnident = format!("interface-{}-{}-write", f.field.name, b.name);
                matches.push(RExpr::block(vec![(
                    structident,
                    RExpr::fncall(
                        String::from("ast-interpret"),
                        vec![
                            RExpr::var(String::from("b")),
                            RExpr::fncall(
                                fnident,
                                vec![
                                    RExpr::var(String::from("st")),
                                    RExpr::var(String::from("v")),
                                ],
                            ),
                        ],
                    ),
                )]));
            }

            let structident = format!("(Op_Iface_{}_ReadAction)", f.field.name);
            let fnident = format!("interface-{}-read-action", f.field.name);
            matches.push(RExpr::block(vec![(
                structident,
                RExpr::fncall(
                    String::from("ast-interpret"),
                    vec![
                        RExpr::var(String::from("b")),
                        RExpr::fncall(fnident, vec![RExpr::var(String::from("st"))]),
                    ],
                ),
            )]));

            let structident = format!("(Op_Iface_{}_WriteAction)", f.field.name);
            let fnident = format!("interface-{}-write-action", f.field.name);
            matches.push(RExpr::block(vec![(
                structident,
                RExpr::fncall(
                    String::from("ast-interpret"),
                    vec![
                        RExpr::var(String::from("b")),
                        RExpr::fncall(fnident, vec![RExpr::var(String::from("st"))]),
                    ],
                ),
            )]));
        }

        let body = RExpr::fncall(
            String::from("destruct"),
            vec![
                RExpr::var(String::from("prog")),
                RExpr::block(vec![(
                    String::from("(Seq s b)"),
                    RExpr::fncall(String::from("destruct"), matches),
                )]),
                RExpr::block(vec![(String::from("_"), RExpr::var(String::from("st")))]),
            ],
        );

        let mut fdef = FunctionDef::new(fname, args, vec![body]);
        fdef.add_comment(String::from("interprets the grammar"));
        rkt.add_function_def(fdef);
    }

    fn add_check_translate(rkt: &mut RosetteFile) {
        rkt.add_section(String::from("Correctness Property"));

        // add assumes clauses for va, pa, size, flags
        // w.r.t: sizes, alignments, etc.
        // those can come from the requires clauses from the map method

        let defs = vec![(
            String::from("st"),
            RExpr::fncall(String::from("make-model"), vec![]),
        )];
        let body = vec![
            RExpr::fncall(
                String::from("set!"),
                vec![
                    RExpr::var(String::from("st")),
                    RExpr::fncall(
                        String::from("ast-interpret"),
                        vec![
                            RExpr::fncall(
                                String::from("impl"),
                                vec![
                                    RExpr::var(String::from("st")),
                                    RExpr::var(String::from("va")),
                                    RExpr::var(String::from("pa")),
                                    RExpr::var(String::from("size")),
                                    RExpr::var(String::from("flags")),
                                ],
                            ),
                            RExpr::var(String::from("st")),
                        ],
                    ),
                ],
            ),
            RExpr::assert(RExpr::bveq(
                RExpr::fncall(
                    String::from("translate"),
                    vec![
                        RExpr::var(String::from("st")),
                        RExpr::var(String::from("va")),
                        RExpr::var(String::from("flags")),
                    ],
                ),
                RExpr::var(String::from("pa")),
            )),
        ];

        let fdef = FunctionDef::new(
            String::from("ast-check-translate"),
            vec![
                String::from("impl"),
                String::from("st"),
                String::from("va"),
                String::from("pa"),
                String::from("size"),
                String::from("flags"),
            ],
            vec![RExpr::letexpr(defs, body)],
        );

        rkt.add_function_def(fdef);
        // add a let expr
        //     (let ([st (make-model)])
        //     ; evaluate the implementation, update the state
        //     (set! st (ast-interpret (impl st va pa size flags) st))

        //     ; now check if the translation is right
        //     (assert (bveq (translate st va 0) pa))
        //   )
    }

    fn add_synthesis(rkt: &mut RosetteFile) {
        rkt.add_section(String::from("Solving / Synthesis"));

        rkt.add_subsection(String::from("Symbolic Variables"));
        // TODO: check the types here?
        rkt.add_new_symbolic_var(String::from("va"), String::from("int64?"));
        rkt.add_new_symbolic_var(String::from("pa"), String::from("int64?"));
        rkt.add_new_symbolic_var(String::from("size"), String::from("int64?"));
        rkt.add_new_symbolic_var(String::from("flags"), String::from("int64?"));

        // the map function
        let fname = String::from("do-synth");
        let args = vec![
            String::from("st"),
            String::from("va"),
            String::from("pa"),
            String::from("size"),
            String::from("flags"),
        ];
        let body = vec![RExpr::fncall(
            String::from("ast-grammar"),
            vec![
                RExpr::var(String::from("st")),
                RExpr::var(String::from("va")),
                RExpr::var(String::from("pa")),
                RExpr::var(String::from("size")),
                RExpr::var(String::from("flags")),
                // RExpr::param(String::from("depty")),
                // RExpr::var(String::from("5")),
            ],
        )];
        let mut fdef = FunctionDef::new(fname, args, body);
        fdef.add_comment(String::from("interprets the grammar"));
        rkt.add_function_def(fdef);

        let body = RExpr::fncall(
            String::from("synthesize"),
            vec![
                RExpr::param(String::from("forall")),
                RExpr::fncall(
                    String::from("list"),
                    vec![
                        RExpr::var(String::from("va")),
                        RExpr::var(String::from("pa")),
                        RExpr::var(String::from("size")),
                        RExpr::var(String::from("flags")),
                    ],
                ),
                RExpr::param(String::from("guarantee")),
                RExpr::fncall(
                    String::from("ast-check-translate"),
                    vec![
                        RExpr::var(String::from("do-synth")),
                        RExpr::var(String::from("va")),
                        RExpr::var(String::from("pa")),
                        RExpr::var(String::from("size")),
                        RExpr::var(String::from("flags")),
                    ],
                ),
            ],
        );
        let vdef = VarDef::new(String::from("sol"), body);
        rkt.add_var(vdef);

        rkt.add_expr(RExpr::fncall(
            String::from("generate-forms"),
            vec![RExpr::var(String::from("sol"))],
        ));
    }

    /// synthesizes the `map` function and returns an ast of it
    pub fn synth_map(&self, ast: &AstRoot) -> Result<Method, SynthError> {
        fs::create_dir_all(&self.outdir)?;

        for unit in &ast.units {
            println!("synthesizing map: for {} in {:?}", unit.name, self.outdir);
            let rktfilepath = self.outdir.join(format!("{}.rkt", unit.name));
            let doc = format!("Unit: {}, Function: map()", unit.name);

            let mut rkt = RosetteFile::new(rktfilepath, doc);

            SynthRosette::add_requires(&mut rkt);
            SynthRosette::add_bitvector_defs(&mut rkt);
            SynthRosette::add_state_fields(&mut rkt, &unit.state);
            SynthRosette::add_interface_fields(&mut rkt, &unit.interface);

            SynthRosette::add_model(&mut rkt);
            SynthRosette::add_model_state_accessors(&mut rkt, &unit.state);
            SynthRosette::add_model_iface_accessors(&mut rkt, &unit.interface);
            SynthRosette::add_actions(&mut rkt, &unit.interface);

            SynthRosette::add_methods(&mut rkt, &unit.methods);

            for m in unit.methods.iter() {
                if m.name == "translate" {
                    SynthRosette::add_translate(&mut rkt, m);
                }
            }

            SynthRosette::add_grammar(&mut rkt, &unit.interface);
            SynthRosette::add_interp_function(&mut rkt, &unit.interface);
            SynthRosette::add_check_translate(&mut rkt);
            SynthRosette::add_synthesis(&mut rkt);

            // TODO: USE BEGIN

            rkt.save();
            rkt.synth();
        }

        Ok(Method::new(String::from("map"), Type::Boolean, Vec::new()))
    }

    /// synthesizes the 'unmap' function and returns an ast of it
    pub fn synth_unmap(&self, ast: &AstRoot) -> Result<Method, SynthError> {
        for unit in &ast.units {
            println!("synthesizing map: for {} in {:?}", unit.name, self.outdir);
        }

        Ok(Method::new(
            String::from("unmap"),
            Type::Boolean,
            Vec::new(),
        ))
    }

    pub fn synth_protect(&self, ast: &AstRoot) -> Result<Method, SynthError> {
        for unit in &ast.units {
            println!("synthesizing map: for {} in {:?}", unit.name, self.outdir);
        }

        Ok(Method::new(
            String::from("protect"),
            Type::Boolean,
            Vec::new(),
        ))
    }
}
