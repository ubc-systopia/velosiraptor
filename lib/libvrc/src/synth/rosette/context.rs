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

//! Synthesis Context Module: Rosette

// std library imports
use std::path::PathBuf;

// rosette language library imports
use rosettelang::{RExpr, RosetteFile};

// crate imports
use crate::synth::COPYRIGHT;

/// adds the requires clauses to the rosette context
fn add_requires(rkt: &mut RosetteFile) {
    rkt.add_new_require(String::from("rosette/lib/synthax"));
    rkt.add_new_require(String::from("rosette/lib/destruct"));
}

/// adds bitvector definitions to the Rosette file context
fn add_bitvector_defs(rkt: &mut RosetteFile) {
    for x in [64, 32, 16, 8] {
        let ident = format!("int{}?", x);
        let arg = format!("{}", x);
        rkt.add_new_var(
            ident,
            RExpr::fncall(String::from("bitvector"), vec![RExpr::var(arg)]),
        );
    }

    let ident = String::from("int?");
    let arg = String::from("68");
    rkt.add_new_var(
        ident,
        RExpr::fncall(String::from("bitvector"), vec![RExpr::var(arg)]),
    );

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

    let ident = String::from("int");
    let arg = String::from("i");
    let arg2 = String::from("int?");
    rkt.add_new_function_def(
        ident,
        vec![arg.clone()],
        vec![RExpr::fncall(
            String::from("bv"),
            vec![RExpr::var(arg), RExpr::var(arg2)],
        )],
    );
}

// prepares the rosette context for synthesis
pub fn prepare_context(name: &str, path: PathBuf) -> RosetteFile {
    let doc = format!("Unit: {}, Function: map()", name);

    let mut rkt = RosetteFile::new(path, doc);
    rkt.add_comment(String::from(COPYRIGHT));

    add_requires(&mut rkt);
    add_bitvector_defs(&mut rkt);

    rkt
}
