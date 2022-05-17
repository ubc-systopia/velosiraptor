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
use super::fields;
use crate::ast::State;

/// the state fields name
pub const STATEFIELDS: &str = "statefields";

pub fn add_state_def(rkt: &mut RosetteFile, state: &State) {
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

        fields::add_slice_accessors(rkt, "state", f);
    }
}
