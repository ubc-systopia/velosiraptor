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

//! # VelosiAst - Slice Expressions
//!
//! This module contains the definitions of the slice AST nodes.

// used standard library functionality
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::{VelosiParseTreeSliceExpr, VelosiTokenStream};

// used crate functionality
use crate::error::VelosiAstIssues;
use crate::{ast_result_return, ast_result_unwrap, AstResult, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{VelosiAstExpr, VelosiAstIdentLiteralExpr, VelosiAstRangeExpr, VelosiAstTypeInfo};

///////////////////////////////////////////////////////////////////////////////////////////////////
// Slice Expression
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an boolean literal expression
#[derive(Eq, Clone)]
pub struct VelosiAstSliceExpr {
    pub ident: VelosiAstIdentLiteralExpr,
    pub range: VelosiAstRangeExpr,
    pub loc: VelosiTokenStream,
}

impl VelosiAstSliceExpr {
    pub fn new(
        ident: VelosiAstIdentLiteralExpr,
        range: VelosiAstRangeExpr,
        loc: VelosiTokenStream,
    ) -> Self {
        VelosiAstSliceExpr { ident, range, loc }
    }
    pub fn from_parse_tree(
        pt: VelosiParseTreeSliceExpr,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // process the function call arguments

        let range = ast_result_unwrap!(VelosiAstRangeExpr::from_parse_tree(pt.range, st), issues);
        let name = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.name, st), issues);

        if let VelosiAstExpr::Range(r) = range {
            if let VelosiAstExpr::IdentLiteral(n) = name {
                let res = VelosiAstExpr::Slice(Self::new(n, r, pt.loc));
                ast_result_return!(res, issues)
            } else {
                unreachable!("should always return a literal expression")
            }
        } else {
            unreachable!("should always return a range expression")
        }
    }

    pub fn flatten(
        self,
        st: &mut SymbolTable,
        mapping: &HashMap<Rc<String>, &VelosiAstExpr>,
    ) -> VelosiAstExpr {
        if let VelosiAstExpr::Range(x) = self.range.flatten(st, mapping) {
            VelosiAstExpr::Slice(Self::new(self.ident, x, self.loc))
        } else {
            unreachable!("should always return a range expression")
        }
    }

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        &VelosiAstTypeInfo::Integer
    }

    /// obtains a reference to the identifier
    pub fn ident(&self) -> &Rc<String> {
        self.ident.ident()
    }

    /// obtains a copy of the identifer
    pub fn ident_to_string(&self) -> String {
        self.ident.ident_to_string()
    }

    /// obtains a reference to the fully qualified path
    pub fn path(&self) -> &Rc<String> {
        self.ident.path()
    }

    /// obtains a copy of the fully qualified path
    pub fn path_to_string(&self) -> String {
        self.ident.path_to_string()
    }

    pub fn get_interface_references(&self, irefs: &mut HashSet<Rc<String>>) {
        self.ident.get_interface_references(irefs);
        self.range.get_interface_references(irefs);
    }

    pub fn get_state_references(&self, srefs: &mut HashSet<Rc<String>>) {
        self.ident.get_state_references(srefs);
        self.range.get_state_references(srefs);
    }

    pub fn has_state_references(&self) -> bool {
        self.ident.has_state_references() || self.range.has_state_references()
    }

    pub fn has_var_references(&self, vars: &HashSet<&str>) -> bool {
        self.ident.has_var_references(vars) || self.range.has_var_references(vars)
    }

    pub fn has_interface_references(&self) -> bool {
        self.ident.has_interface_references() || self.range.has_interface_references()
    }

    pub fn get_var_references(&self) -> HashSet<&VelosiAstIdentLiteralExpr> {
        self.ident.get_var_references()
    }
}

/// Implementation of [PartialEq] for [VelosiAstSliceExpr]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstSliceExpr {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident && self.range == other.range
    }
}

/// Implementation of [Hash] for [VelosiAstSliceExpr]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstSliceExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ident.hash(state);
        self.range.hash(state);
    }
}

impl Display for VelosiAstSliceExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(
            format,
            "{}[{}..{}]",
            self.path(),
            self.range.start,
            self.range.end
        )
    }
}

/// Implementation of [Debug] for [VelosiAstSliceExpr]
impl Debug for VelosiAstSliceExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
