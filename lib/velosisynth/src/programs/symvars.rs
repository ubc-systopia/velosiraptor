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

//! Synthesis Module: Symbolic Variables

use smt2::{Smt2Context, Term, VarDecl};

use crate::model;

pub struct SymbolicVars {
    counter: usize,
}

impl SymbolicVars {
    pub fn new() -> Self {
        Self { counter: 0 }
    }

    pub fn get(&mut self) -> String {
        let name = format!("symvar!{}", self.counter);
        self.counter += 1;
        name
    }

    pub fn add_to_context(&self, smt: &mut Smt2Context) {
        smt.comment("Variable Definitions".to_string());
        for i in 0..self.counter {
            let name = format!("symvar!{}", i);
            smt.variable(VarDecl::new(name, model::types::num()));
        }
    }

    pub fn add_get_values(&self, smt: &mut Smt2Context) {
        smt.comment("Get Values".to_string());
        if self.counter == 0 {
            smt.echo("()".to_string());
            return;
        }
        let mut terms = Vec::new();
        for i in 0..self.counter {
            let name = format!("symvar!{}", i);
            terms.push(Term::ident(name));
        }

        smt.get_value(terms);
    }
}

impl Default for SymbolicVars {
    fn default() -> Self {
        Self::new()
    }
}
