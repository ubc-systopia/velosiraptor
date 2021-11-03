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
use crate::ast::{AstRoot, BitSlice, Interface, Method, State, Type};
use crate::synth::SynthError;
use rosettelang::{FunctionDef, RExpr, RosetteFile, StructDef};

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

    fn add_bitvector_defs(rkt: &mut RosetteFile) {}

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
        let mask = (1u64 << (bslice.end - bslice.start + 1)) - 1;
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
            let body = RExpr::matchexpr(
                statevar.clone(),
                vec![
                    (
                        RExpr::fncall(
                            String::from(STATEFIELDS),
                            vec![RExpr::var(String::from("e"))],
                        ),
                        vec![RExpr::var(String::from("e"))],
                    ),
                    (
                        RExpr::var(String::from("_")),
                        vec![
                            RExpr::fncall(
                                String::from("printf"),
                                vec![RExpr::text(String::from("wrong state supplied"))],
                            ),
                            RExpr::var(String::from("e")),
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
        //let entries = iface.fields().iter().map(|f|{ f.name.clone() }).collect::<Vec<String>>();
        let entries = Vec::new();
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

            let fname = format!("iface-fields-load-{}", f.field.name);
            let args = vec![statevar.clone()];
            let body = RExpr::matchexpr(
                statevar.clone(),
                vec![
                    (
                        RExpr::fncall(
                            String::from(IFACEFIELDS),
                            vec![RExpr::var(String::from("e"))],
                        ),
                        vec![RExpr::var(String::from("e"))],
                    ),
                    (
                        RExpr::var(String::from("_")),
                        vec![
                            RExpr::fncall(
                                String::from("printf"),
                                vec![RExpr::text(String::from("wrong state supplied"))],
                            ),
                            RExpr::var(String::from("e")),
                        ],
                    ),
                ],
            );
            let mut fdef = FunctionDef::new(fname, args, vec![body]);
            fdef.add_comment(String::from("Field accessor"));
            rkt.add_function_def(fdef);

            let fname = format!("iface-fields-store-{}", f.field.name);
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
                SynthRosette::add_insert_extract(rkt, "iface", &f.field.name, f.field.length, b);
                SynthRosette::add_read_write_slice(rkt, "iface", &f.field.name, &b.name)
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
                        RExpr::var(String::from("e")),
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

        let fnname = String::from("model-get-iface");
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
                        RExpr::var(String::from("e")),
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

        let fnname = String::from("model-set-iface");
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
            format!("{}-fields-{}-read", ftype, fieldname),
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
            rkt.add_subsection(format!("iface field: {}", f.field.name));

            SynthRosette::add_model_field_accessor(rkt, "iface", &f.field.name);

            for b in &f.field.layout {
                SynthRosette::add_model_slice_accessor(rkt, "iface", &f.field.name, &b.name);
            }
        }
    }

    fn add_actions(rkt: &mut RosetteFile, iface: &Interface) {
        rkt.add_section(String::from("Actions"));
        let stvar = String::from("st");
        for f in iface.fields() {
            rkt.add_subsection(format!("iface field: {}", f.field.name));

            // write actions

            let fname = format!("interface-{}-write-action", f.field.name);
            let args = vec![stvar.clone()];

            let mut fdef = FunctionDef::new(fname, args, vec![]);
            fdef.add_comment(format!("performs the write actions of {}", f.field.name));
            rkt.add_function_def(fdef);

            // read actions

            let fname = format!("interface-{}-read-action", f.field.name);
            let args = vec![stvar.clone()];

            let mut fdef = FunctionDef::new(fname, args, vec![]);
            fdef.add_comment(format!("performs the read actions of {}", f.field.name));
            rkt.add_function_def(fdef);
        }
    }

    fn add_translate(rkt: &mut RosetteFile) {
        rkt.add_section(String::from("Translation Function"));
    }

    fn add_grammar(rkt: &mut RosetteFile, iface: &Interface) {
        rkt.add_section(String::from("Grammar Definition"));
    }

    fn add_interp_function(rkt: &mut RosetteFile, iface: &Interface) {
        rkt.add_section(String::from("Interpretation Function"));
    }

    fn add_check_translate(rkt: &mut RosetteFile) {
        rkt.add_section(String::from("Correctness Property"));
    }

    fn add_synthesis(rkt: &mut RosetteFile) {
        rkt.add_section(String::from("Solving / Synthesis"));
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
            SynthRosette::add_translate(&mut rkt);
            SynthRosette::add_grammar(&mut rkt, &unit.interface);
            SynthRosette::add_interp_function(&mut rkt, &unit.interface);
            SynthRosette::add_check_translate(&mut rkt);
            SynthRosette::add_synthesis(&mut rkt);

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
