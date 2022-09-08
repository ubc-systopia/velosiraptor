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

// std library imports

// rosette language library imports
use rosettelang::{FunctionDef, RExpr, RosetteFile, StructDef};

// crate imports
use super::fields;
use crate::ast::Interface;

pub const IFACEFIELDS: &str = "ifacefields";

pub fn add_interface_def(rkt: &mut RosetteFile, iface: &Interface) {
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
            .enumerate()
            //.map(|(i, _f)| RExpr::listelm(String::from("v"), (i + 1) as u64))
            .map(|_| RExpr::num(64, 0))
            .collect::<Vec<RExpr>>(),
    );

    // let body = iface
    //     .fields()
    //     .iter()
    //     .fold(RExpr::var(String::from("#hash()")), |acc, x| {
    //         RExpr::fncall(
    //             String::from("dict-set"),
    //             vec![
    //                 acc,
    //                 RExpr::var(format!("'{}", x.field.name)),
    //                 RExpr::num(64, 0),
    //             ],
    //         )
    //     });

    let mut f = FunctionDef::new(
        String::from("make-iface-fields"),
        vec![String::from("v")],
        vec![body],
    );
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
        // let body = RExpr::fncall(String::from("dict-ref"),
        //     vec![RExpr::var(statevar.clone()), RExpr::var(format!("'{}", f.field.name)),
        //     ]);
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

        // let body = RExpr::fncall(String::from("dict-set"),
        //             vec![RExpr::var(statevar.clone()), RExpr::var(format!("'{}", f.field.name)),
        //             RExpr::var(valvar.clone())
        //             ]);

        let mut fdef = FunctionDef::new(fname, args, vec![body]);
        fdef.add_comment(String::from("Field update"));
        rkt.add_function_def(fdef);

        fields::add_slice_accessors(rkt, "interface", &f.field);
    }
}
