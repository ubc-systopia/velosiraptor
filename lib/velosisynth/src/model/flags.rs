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

//! Const Synthesis Module: Rosette

// rosette language library imports
use smt2::{Attribute, Function, Smt2Context, SortedVar, Term};

use velosiast::ast::VelosiAstFlags;

// crate imports
use super::{types, utils};

pub fn flags_get_fn_name(prefix: &str, flag: &str) -> String {
    utils::with_prefix(prefix, &format!("Flags.{flag}.get!"))
}

pub fn add_flags(smt: &mut Smt2Context, ctxt: &str, flags: &VelosiAstFlags) {
    smt.section(format!("flags for unit {} ({:?}", ctxt, flags.loc.loc()));

    for (i, flag) in flags.flags.iter().enumerate() {
        // the get() function extracting the bit fields
        let f_get_fn_name = flags_get_fn_name(ctxt, flag.as_str());

        //
        // Define the Function
        //
        let mut f = Function::new(f_get_fn_name.clone(), types::num(ctxt));
        f.add_arg("flgs".to_string(), types::flags(ctxt));
        smt.function(f);

        //
        // Assert the function body
        //

        let e = Term::bveq(
            Term::fn_apply(
                f_get_fn_name.clone(),
                vec![Term::ident("flgs@".to_string())],
            ),
            Term::bvand(
                Term::bvshr(Term::ident("flgs@".to_string()), Term::num(i as u64)),
                Term::num(1),
            ),
        );
        let attrs = vec![
            Attribute::with_value("pattern".to_string(), format!("(({f_get_fn_name} flgs@))")),
            Attribute::with_value("qid".to_string(), f_get_fn_name.clone()),
            Attribute::with_value("skolemid".to_string(), format!("skolem_{}", f_get_fn_name)),
        ];

        let e = Term::attributed(e, attrs);
        smt.assert(Term::forall(
            vec![SortedVar::new("flgs@".to_string(), types::flags(ctxt))],
            e,
        ));
    }
}
