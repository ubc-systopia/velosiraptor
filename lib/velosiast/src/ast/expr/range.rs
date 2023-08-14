// Velosiraptor AST
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

//! # VelosiAst - Range Expressions
//!
//! This module contains the definitions of the range AST nodes.

// used standard library functionality
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeRangeExpr;
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::VelosiAstIssues;
use crate::{ast_result_return, ast_result_unwrap, AstResult, SymbolTable, VelosiAstErrBuilder};

// used definitions of references AST nodes
use crate::ast::{VelosiAstExpr, VelosiAstIdentLiteralExpr};

///////////////////////////////////////////////////////////////////////////////////////////////////
// Range Expression
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an boolean literal expression
#[derive(Eq, Clone)]
pub struct VelosiAstRangeExpr {
    pub start: u64,
    pub end: u64,
    pub loc: VelosiTokenStream,
}

impl VelosiAstRangeExpr {
    pub fn new(start: u64, end: u64, loc: VelosiTokenStream) -> Self {
        VelosiAstRangeExpr { start, end, loc }
    }
    pub fn from_parse_tree(
        pt: VelosiParseTreeRangeExpr,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();
        let e = ast_result_unwrap!(Self::from_parse_tree_raw(pt, st), issues);
        ast_result_return!(VelosiAstExpr::Range(e), issues)
    }

    pub fn from_parse_tree_raw(
        pt: VelosiParseTreeRangeExpr,
        _st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

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

        ast_result_return!(Self::new(pt.start, pt.end, pt.loc), issues)
    }

    pub fn is_const(&self) -> bool {
        true
    }

    pub fn try_get_start_limit(&self) -> Option<(u64, u64)> {
        if self.end > 0 {
            Some((self.start, self.end - 1))
        } else {
            None
        }
    }

    pub fn flatten(
        self,
        st: &mut SymbolTable,
        mapping: &HashMap<Rc<String>, &VelosiAstExpr>,
    ) -> VelosiAstExpr {
        VelosiAstExpr::Range(self.flatten_raw(st, mapping))
    }

    pub fn flatten_raw(
        self,
        _st: &mut SymbolTable,
        _mapping: &HashMap<Rc<String>, &VelosiAstExpr>,
    ) -> Self {
        self
    }

    pub fn get_interface_references(&self, _irefs: &mut HashSet<Rc<String>>) {
        /* no-op */
    }

    pub fn get_state_references(&self, _srefs: &mut HashSet<Rc<String>>) {
        /* no-op */
    }

    pub fn has_state_references(&self) -> bool {
        false
    }

    pub fn has_var_references(&self, _vars: &HashSet<&str>) -> bool {
        false
    }

    pub fn has_interface_references(&self) -> bool {
        false
    }

    pub fn get_var_references(&self) -> HashSet<&VelosiAstIdentLiteralExpr> {
        HashSet::new()
    }
}

/// Implementation of [PartialEq] for [VelosiAstRangeExpr]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstRangeExpr {
    fn eq(&self, other: &Self) -> bool {
        self.start == other.start && self.end == other.end
    }
}

/// Implementation of [Hash] for [VelosiAstRangeExpr]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstRangeExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.start.hash(state);
        self.end.hash(state);
    }
}

impl Display for VelosiAstRangeExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}..{}", self.start, self.end)
    }
}

/// Implementation of [Debug] for [VelosiAstRangeExpr]
impl Debug for VelosiAstRangeExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
