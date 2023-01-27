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

// used standard library components
use std::rc::Rc;

// external library imports
use smt2::{Smt2Context, Term};
use velosiast::ast::VelosiAstConst;

// crate imports
use crate::model::types;

/// adds constant definitions to the current context
pub fn add_consts(smt: &mut Smt2Context, context: &str, consts: &[Rc<VelosiAstConst>]) {
    smt.section(format!("Constants for unit {context}"));
    for c in consts {
        if c.ctype.is_numeric() {
            let val = c
                .try_into_u64()
                .expect("Expected numeric constant but could not convert.");
            smt.constant(c.ident_to_string(), types::num(), Term::num(val));
        } else if c.ctype.is_boolean() {
            let val = c
                .try_into_bool()
                .expect("Expected boolean constant but could not convert.");
            smt.constant(c.ident_to_string(), types::num(), Term::Binary(val));
        } else {
            unreachable!("constant with type `{}` unhandled\n", c.ctype);
        }
    }
}
