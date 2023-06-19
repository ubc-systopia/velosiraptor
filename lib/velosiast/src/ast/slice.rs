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
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use velosiparser::VelosiParseTreeFieldSlice;

use crate::ast::{VelosiAstIdentifier, VelosiAstNode, VelosiAstType};
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, utils, AstResult, Symbol, VelosiTokenStream};

#[derive(Eq, Clone, Debug)]
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
            let msg = format!("End of range exceeds maximum number of bits of field ({maxbits}).");
            let hint = "Reduce the end of the range.";
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint.to_string())
                .add_location(pt.loc.from_self_with_subrange(2..3))
                .build();
            issues.push(err);
        }

        ast_result_return!(Self::new(ident, pt.start, pt.end, pt.loc), issues)
    }

    /// obtains a reference to the identifier
    pub fn ident(&self) -> &Rc<String> {
        self.ident.ident()
    }

    /// obtains a copy of the identifer
    pub fn ident_to_string(&self) -> String {
        self.ident.as_str().to_string()
    }

    /// obtains a reference to the fully qualified path
    pub fn path(&self) -> &Rc<String> {
        &self.ident.path
    }

    /// obtains a copy of the fully qualified path
    pub fn path_to_string(&self) -> String {
        self.ident.path.as_str().to_string()
    }

    /// constructs the mask value of the bit slice
    pub fn mask(&self) -> u64 {
        let mut mask = 0;
        for i in self.start..self.end {
            mask |= 1 << i;
        }
        mask
    }

    pub fn nbits(&self) -> u64 {
        self.end - self.start
    }
}

impl PartialOrd for VelosiAstFieldSlice {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for VelosiAstFieldSlice {
    fn cmp(&self, other: &Self) -> Ordering {
        // if the start is smaller, then we're smaller
        if self.start < other.start {
            return Ordering::Less;
        }

        if self.start > other.start {
            return Ordering::Greater;
        }

        // if the end is smaller, then we're smaller

        if self.end < other.end {
            return Ordering::Less;
        }

        if self.end > other.end {
            return Ordering::Greater;
        }

        // finally just consider the identifier

        self.ident.cmp(&other.ident)
    }
}

impl PartialEq for VelosiAstFieldSlice {
    fn eq(&self, other: &Self) -> bool {
        self.start == other.start && self.end == other.end && self.ident == other.ident
    }
}

/// Implementation fo the [From] trait for [Symbol] for conversion to symbol
impl From<Rc<VelosiAstFieldSlice>> for Symbol {
    fn from(f: Rc<VelosiAstFieldSlice>) -> Self {
        let n = VelosiAstNode::StateFieldSlice(f.clone());
        Symbol::new(f.path().clone(), VelosiAstType::new_int(), n)
    }
}

/// Implementation of [Display] for [VelosiAstFieldSlice]
impl Display for VelosiAstFieldSlice {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}..{} {}", self.start, self.end, self.path())
    }
}
