// Velosiraptor Synthesizer
//
//
// MIT License
//
// Copyright (c) 2023 Systopia Lab, Computer Science, University of British Columbia
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

use velosiast::ast::{VelosiAstExpr, VelosiAstUnitSegment};

use crate::error::VelosiSynthIssues;

use crate::z3::Z3WorkerPool;

/// checks the methods for
pub fn check_unit(z3: &mut Z3WorkerPool, unit: &VelosiAstUnitSegment) -> VelosiSynthIssues {
    let _issues = VelosiSynthIssues::new();

    // collect all the expressions
    let mut exprs: Vec<&VelosiAstExpr> = Vec::new();
    for m in unit.methods() {
        exprs.extend(m.requires.iter().map(|e| e.as_ref()));
        if let Some(body) = m.body.as_ref() {
            if m.rtype.is_boolean() {
                exprs.push(body);
            }
        }
    }

    // now we have all the expressions in an array
    let issues = super::check_all_expr(z3, exprs.as_slice());
    if issues.is_ok() {
        return issues;
    }

    let issues_new = super::check_all_expr_pairwise(z3, exprs.as_slice());

    if issues_new.is_ok() {
        return issues;
    }
    issues_new
}
