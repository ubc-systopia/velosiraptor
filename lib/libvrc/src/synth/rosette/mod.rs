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

impl SynthRosette {
    pub fn new(outdir: &Path, pkg: String) -> Self {
        SynthRosette {
            outdir: outdir.join(&pkg).join("synth"),
            pkg,
        }
    }

    fn add_bitvector_defs(rkt: &mut RosetteFile) {}

    fn add_requires(rkt: &mut RosetteFile) {
        rkt.add_new_require(String::from("rosette/lib/syntax"));
        rkt.add_new_require(String::from("rosette/lib/destruct"));
    }

    fn add_insert_extract(rkt: &mut RosetteFile, field: &str, bslice: &BitSlice) {
        let fieldsize = 64;
        let mask = (1u64 << (bslice.end - bslice.start + 1)) - 1;
        let varname = String::from("val");
        let oldname = String::from("old");

        // extract function
        let fname = format!("state-fields-{}-{}-extract", field, bslice.name);
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
        let fname = format!("state-fields-{}-{}-insert", field, bslice.name);
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

    fn add_read_write_slice(rkt: &mut RosetteFile, field: &str, bslice: &str) {
        let varname = String::from("val");
        let stname = String::from("st");

        let fname = format!("state-fields-{}-{}-read", field, bslice);
        let args = vec![stname.clone()];
        let body = RExpr::fncall(
            format!("state-fields-{}-{}-extract", field, bslice),
            vec![RExpr::fncall(
                format!("state-fields-load-{}", field),
                vec![RExpr::var(stname.clone())],
            )],
        );
        let mut fdef = FunctionDef::new(fname, args, vec![body]);
        fdef.add_comment(format!(
            "reads '{}' bits from '{}' field value",
            field, bslice
        ));
        rkt.add_function_def(fdef);

        let fname = format!("state-fields-{}-{}-write", field, bslice);
        let args = vec![stname.clone(), varname.clone()];
        let body = RExpr::fncall(
            format!("state-fields-store-{}", field),
            vec![
                RExpr::var(stname.clone()),
                RExpr::fncall(
                    format!("state-fields-{}-{}-insert", field, bslice),
                    vec![
                        RExpr::fncall(
                            format!("state-fields-load-{}", field),
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
                SynthRosette::add_insert_extract(rkt, &f.name, b);
                SynthRosette::add_read_write_slice(rkt, &f.name, &b.name)
            }
        }
    }

    fn add_interface_fields(rkt: &mut RosetteFile, iface: &Interface) {
        rkt.add_section(String::from("Interface Fields"));

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

        let mut f = FunctionDef::new(String::from("make-state-iface"), Vec::new(), Vec::new());
        f.add_comment(String::from("Interface Constructor"));
        rkt.add_function_def(f);
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
