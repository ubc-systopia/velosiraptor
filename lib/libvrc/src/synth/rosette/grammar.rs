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
use std::collections::{HashMap, HashSet};

// rosette language library imports
use rosettelang::{FunctionDef, RExpr, RosetteFile};

// crate imports
use crate::ast::Interface;

fn add_grammar_def(
    rkt: &mut RosetteFile,
    iface: &Interface,
    state_syms: &HashSet<String>,
    state_bits: &HashMap<String, u64>,
) {
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
    // filter

    let st_access_fields = iface.fields_accessing_state(state_syms, state_bits);
    for f in iface.fields() {
        //let fieldref = format!("interface.{}", f.field.name);
        // if !st_access_fields.contains(&fieldref) {
        //     println!("skipping: {}", fieldref);
        //     continue;
        // }

        for b in &f.field.layout {
            //let n = format!("interface.{}.{}", f.field.name, b.name);
            // if !st_access_fields.contains(&n) {
            //     println!("skipping2: {}", n);
            //     continue;
            // }

            let arg = String::from("arg");
            let ident = format!("Op-Iface-{}-{}-Insert", f.field.name, b.name);
            rkt.add_new_struct_def(ident, vec![arg], String::from("#:transparent"));
        }
        let ident = format!("Op-Iface-{}-WriteAction", f.field.name);
        rkt.add_new_struct_def(ident, vec![], String::from("#:transparent"));
        let ident = format!("Op-Iface-{}-ReadAction", f.field.name);
        rkt.add_new_struct_def(ident, vec![], String::from("#:transparent"));
    }

    // now define the grammar
    let fname = String::from("ast-grammar");
    let args = vec![
        String::from("va"),
        String::from("size"),
        String::from("flags"),
        String::from("pa"),
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
        let fieldref = format!("interface.{}", f.field.name);
        if !st_access_fields.contains(&fieldref) {
            ops.push(RExpr::comment(format!("skipped: {}", fieldref)));
            continue;
        }

        for b in &f.field.layout {
            let n = format!("interface.{}.{}", f.field.name, b.name);
            if !st_access_fields.contains(&n) {
                ops.push(RExpr::comment(format!("skipped: {}", n)));
                continue;
            }

            // let arg = String::from("arg");
            let ident = format!("Op-Iface-{}-{}-Insert", f.field.name, b.name);
            let args = RExpr::fncall(String::from("binop"), vec![]);
            ops.push(RExpr::fncall(ident, vec![args]));
        }
        let ident = format!("Op-Iface-{}-WriteAction", f.field.name);
        ops.push(RExpr::fncall(ident, vec![]));
        let ident = format!("Op-Iface-{}-ReadAction", f.field.name);
        ops.push(RExpr::fncall(ident, vec![]));
    }
    body.push(RExpr::block(vec![(
        String::from("ops"),
        RExpr::fncall(String::from("choose"), ops),
    )]));

    body.push(RExpr::block(vec![(
        String::from("binop"),
        RExpr::fncall(
            String::from("choose"),
            vec![
                RExpr::var(String::from("(valexpr)")),
                RExpr::var(String::from("(bvshl (valexpr) (valexpr))")),
                RExpr::var(String::from("(bvlshr (valexpr) (valexpr))")),
                RExpr::var(String::from(";(bvadd (binop) (valexpr))")),
                RExpr::var(String::from(";(bvand (binop) (valexpr))")),
                RExpr::var(String::from(";(bvor (binop) (valexpr))")),
                RExpr::var(String::from(";(bvmul (binop) (valexpr))")),
                RExpr::var(String::from(";(bvudiv (binop) (valexpr))")),
                RExpr::var(String::from(";(bvurem (binop) (valexpr))")),
            ],
        ),
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
                RExpr::var(String::from("(?? int?)")),
                // RExpr::var(String::from("(?? int32?)")),
                // RExpr::var(String::from("(?? int16?)")),
                // RExpr::var(String::from("(?? int8?)")),
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
            let structident = format!("(Op-Iface-{}-{}-Insert v)", f.field.name, b.name);
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

        let structident = format!("(Op-Iface-{}-ReadAction)", f.field.name);
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

        let structident = format!("(Op-Iface-{}-WriteAction)", f.field.name);
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

pub fn add_grammar(
    rkt: &mut RosetteFile,
    iface: &Interface,
    state_syms: &HashSet<String>,
    state_bits: &HashMap<String, u64>,
) {
    add_grammar_def(rkt, iface, state_syms, state_bits);
    add_interp_function(rkt, iface);
}
