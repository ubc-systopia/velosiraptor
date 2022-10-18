// VelosiAst -- a Ast for the Velosiraptor Language
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

//! Utils Module

use std::rc::Rc;

use velosiparser::VelosiTokenStream;

use crate::ast::VelosiAstNode;
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::SymbolTable;

/// checks if the identifier has snake case
pub fn check_upper_case(issues: &mut VelosiAstIssues, name: &str, loc: VelosiTokenStream) {
    let allupper = name.chars().all(|x| x.is_uppercase());
    if !allupper {
        let msg = format!("identifier `{}` should have an upper case name", name);
        let hint = format!(
            "convert the identifier to upper case (notice the capitalization): `{}`",
            name.to_ascii_uppercase()
        );
        let err = VelosiAstErrBuilder::warn(msg)
            .add_hint(hint)
            .add_location(loc)
            .build();

        issues.push(err);
    }
}

/// checks whether the identifier is in snake_case
pub fn check_snake_case(issues: &mut VelosiAstIssues, name: &str, loc: VelosiTokenStream) {
    let allupper = name.chars().all(|x| x.is_lowercase());
    if !allupper {
        let msg = format!("identifier `{}` should have an snake case name", name);
        let hint = format!(
            "convert the identifier to upper case (notice the snake_case): `{}`",
            name.to_ascii_lowercase()
        );
        let err = VelosiAstErrBuilder::warn(msg)
            .add_hint(hint)
            .add_location(loc)
            .build();

        issues.push(err);
    }
}

/// checks whether the identifier is in snake_case
pub fn check_type_exists(
    issues: &mut VelosiAstIssues,
    st: &SymbolTable,
    name: Rc<String>,
    loc: VelosiTokenStream,
) {
    if let Some(s) = st.lookup(name.as_str()) {
        match s.ast_node {
            // there is a unit with that type, so we're good
            VelosiAstNode::Unit(_) => (),
            _ => {
                // report that there was a mismatching type
                let err = VelosiAstErrUndef::with_other(name, loc, s.loc().clone());
                issues.push(err.into());
            }
        }
    } else {
        // there is no such type, still create the node and report the issue
        let err = VelosiAstErrUndef::new(name, loc);
        issues.push(err.into());
    }
}
