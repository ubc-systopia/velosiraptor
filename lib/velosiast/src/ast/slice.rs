// VelosiAst -- a Ast for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2021, 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiAst -- Field Slices
//!
//! This module defines the Slice AST nodes of the langauge
//!

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use velosiparser::VelosiParseTreeFieldSlice;

use crate::ast::{VelosiAstIdentifier, VelosiAstNode, VelosiAstType};
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, utils, AstResult, Symbol, VelosiTokenStream};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstFieldSlice {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the start of the range
    pub start: u64,
    /// the end of the range (not including)
    pub end: u64,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstFieldSlice {
    pub fn new(ident: VelosiAstIdentifier, start: u64, end: u64, loc: VelosiTokenStream) -> Self {
        Self {
            ident,
            start,
            end,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeFieldSlice,
        field: &str,
        maxbits: u64,
    ) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convert the identifer and check for format
        let ident = VelosiAstIdentifier::from_parse_tree_with_prefix(pt.name, field);
        utils::check_snake_case(&mut issues, &ident);

        // check if we actually have a range
        if pt.start == pt.end {
            let msg = "Empty range.";
            let hint = "Increase the end of the range";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(pt.loc.from_self_with_subrange(0..3))
                .build();
            issues.push(err);
        }

        // check if the range makes sense
        if pt.start > pt.end {
            let msg = "Start of range is smaller than the end.";
            let hint = "Adjust the range bounds.";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(pt.loc.from_self_with_subrange(0..3))
                .build();
            issues.push(err);
        }

        if pt.end > maxbits {
            let msg = format!(
                "End of range exceeds maximum number of bits of field ({}).",
                maxbits
            );
            let hint = "Reduce the end of the range.";
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint.to_string())
                .add_location(pt.loc.from_self_with_subrange(2..3))
                .build();
            issues.push(err);
        }

        ast_result_return!(Self::new(ident, pt.start, pt.end, pt.loc), issues)
    }

    pub fn ident_as_str(&self) -> &str {
        self.ident.name.as_str()
    }

    pub fn ident_as_rc_string(&self) -> Rc<String> {
        self.ident.name.clone()
    }

    pub fn ident_to_string(&self) -> String {
        self.ident.name.to_string()
    }
}

/// Implementation fo the [From] trait for [Symbol] for conversion to symbol
impl From<Rc<VelosiAstFieldSlice>> for Symbol {
    fn from(f: Rc<VelosiAstFieldSlice>) -> Self {
        let n = VelosiAstNode::StateFieldSlice(f.clone());
        Symbol::new(f.ident_as_rc_string(), VelosiAstType::new_int(), n)
    }
}

/// Implementation of [Display] for [VelosiAstFieldSlice]
impl Display for VelosiAstFieldSlice {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "{}..{} {}", self.start, self.end, self.ident.as_str())
    }
}
