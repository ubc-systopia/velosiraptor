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

use crate::ast::{VelosiAstFieldSlice, VelosiAstIdentifier, VelosiAstNode};
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::SymbolTable;

/// checks if the identifier has snake case
pub fn check_upper_case(issues: &mut VelosiAstIssues, id: &VelosiAstIdentifier) {
    let name = id.name.as_str();
    let allupper = name
        .chars()
        .all(|x| x.is_ascii_uppercase() || !x.is_alphanumeric());
    if !allupper {
        let msg = format!("identifier `{}` should have an upper case name", name);
        let hint = format!(
            "convert the identifier to upper case (notice the capitalization): `{}`",
            name.to_ascii_uppercase()
        );
        let err = VelosiAstErrBuilder::warn(msg)
            .add_hint(hint)
            .add_location(id.loc.clone())
            .build();

        issues.push(err);
    }
}

/// checks whether the identifier is in snake_case
pub fn check_snake_case(issues: &mut VelosiAstIssues, id: &VelosiAstIdentifier) {
    let name = id.name.as_str();
    let allupper = name
        .chars()
        .all(|x| x.is_ascii_lowercase() || !x.is_alphabetic());
    if !allupper {
        let msg = format!("identifier `{}` should have an snake case name", name);
        let hint = format!(
            "convert the identifier to lower case (notice the snake_case): `{}`",
            name.to_ascii_lowercase()
        );
        let err = VelosiAstErrBuilder::warn(msg)
            .add_hint(hint)
            .add_location(id.loc.clone())
            .build();

        issues.push(err);
    }
}

/// checks whether the identifier is in snake_case
pub fn check_type_exists(issues: &mut VelosiAstIssues, st: &SymbolTable, id: &VelosiAstIdentifier) {
    let name = id.name.as_str();
    if let Some(s) = st.lookup(name) {
        match s.ast_node {
            // there is a unit with that type, so we're good
            VelosiAstNode::Unit(_) => (),
            _ => {
                // report that there was a mismatching type
                let err = VelosiAstErrUndef::from_ident_with_other(id, s.loc().clone());
                issues.push(err.into());
            }
        }
    } else {
        // there is no such type, still create the node and report the issue
        let err = VelosiAstErrUndef::from_ident(id);
        issues.push(err.into());
    }
}

/// checks whether the identifier is in snake_case
pub fn check_param_exists(
    issues: &mut VelosiAstIssues,
    st: &SymbolTable,
    id: &VelosiAstIdentifier,
) {
    let name = id.name.as_str();
    if let Some(s) = st.lookup(name) {
        match s.ast_node {
            // there is a unit with that type, so we're good
            VelosiAstNode::Param(_) => (),
            _ => {
                // report that there was a mismatching type
                let err = VelosiAstErrUndef::from_ident_with_other(id, s.loc().clone());
                issues.push(err.into());
            }
        }
    } else {
        // there is no such type, still create the node and report the issue
        let err = VelosiAstErrUndef::from_ident(id);
        issues.push(err.into());
    }
}

/// checks whether the identifier is in snake_case
pub fn check_addressing_width(issues: &mut VelosiAstIssues, w: u64, loc: VelosiTokenStream) {
    if w > 64 {
        let msg = "unsupported addressing width: exceeds maximum addressing size of 64 bits";
        let hint = "reduce the addressing width to 64 bits or less";
        let err = VelosiAstErrBuilder::err(msg.to_string())
            .add_hint(hint.to_string())
            .add_location(loc.clone())
            .build();
        issues.push(err);
    }

    if w == 0 {
        let msg = "unsupported addressing width: addressing size is zero";
        let hint = "increase the adressing width";
        let err = VelosiAstErrBuilder::err(msg.to_string())
            .add_hint(hint.to_string())
            .add_location(loc.clone())
            .build();
        issues.push(err);
    }

    if w < 8 {
        let msg = "unusual addressing width: addressing size is very small";
        let hint = "consider increase the adressing width";
        let err = VelosiAstErrBuilder::warn(msg.to_string())
            .add_hint(hint.to_string())
            .add_location(loc)
            .build();
        issues.push(err);
    }
}

/// checks whether the identifier is in snake_case
pub fn check_field_size(issues: &mut VelosiAstIssues, size: u64, loc: &VelosiTokenStream) -> u64 {
    if ![1, 2, 4, 8].contains(&size) {
        if [8, 16, 32, 64].contains(&size) {
            let msg = format!("Size in bits given, bytes expected. Converting to {}", size);
            let hint = "Change the size information to one of 1, 2, 4, 8.";
            let err = VelosiAstErrBuilder::warn(msg)
                .add_hint(hint.to_string())
                .add_location(loc.from_self_with_subrange(7..8))
                .build();
            issues.push(err);
            return size / 8;
        } else {
            let msg = format!("Unsupported size of the memory field: {}", size);
            let hint = "Change the size information to one of 1, 2, 4, 8.";
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint.to_string())
                .add_location(loc.from_self_with_subrange(7..8))
                .build();
            issues.push(err);
        }
    }
    size
}

pub fn slice_overlap_check(
    issues: &mut VelosiAstIssues,
    sizebits: u64,
    slices: &[Rc<VelosiAstFieldSlice>],
) {
    let mut bits: Vec<Option<Rc<VelosiAstFieldSlice>>> = vec![None; sizebits as usize];
    for slice in slices {
        for i in (slice.start as usize)..(slice.end as usize) {
            // overflow captured at another place
            if i >= sizebits as usize {
                break;
            }
            if let Some(s) = &bits[i] {
                let msg = format!("Field slices overlap at bit {}", i);
                let hint = format!("This slices overlaps with slice `{}`", s.ident);
                let related = "This is the slice that overlaps with.";
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint)
                    .add_location(slice.loc.clone())
                    .add_related_location(related.to_string(), s.loc.clone())
                    .build();
                issues.push(err);
                break;
            }
            bits[i] = Some(slice.clone());
        }
    }
}
