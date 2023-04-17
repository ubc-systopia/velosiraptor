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

//! # VelosiAst -- Parameter Definitions
//!
//! This module defines the Parameter AST nodes of the langauge

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use velosiparser::{VelosiParseTreeIdentifier, VelosiParseTreeParam, VelosiTokenStream};

use crate::ast::{
    types::{VelosiAstType, VelosiAstTypeInfo},
    VelosiAstIdentifier, VelosiAstNode,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

#[derive(Eq, Clone, Debug)]
pub struct VelosiAstParam {
    /// the identifier of the constant
    pub ident: VelosiAstIdentifier,
    /// the type of the constant
    pub ptype: VelosiAstType,
    /// the location of the import clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstParam {
    pub fn new(ident: VelosiAstIdentifier, ptype: VelosiAstType, loc: VelosiTokenStream) -> Self {
        Self { ident, ptype, loc }
    }

    pub fn with_name(name: String, ptype: VelosiAstTypeInfo) -> Self {
        VelosiAstParam::new(
            VelosiAstIdentifier::with_name(name),
            ptype.into(),
            VelosiTokenStream::empty(),
        )
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

    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeParam,
        all_types: bool,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        let ident = VelosiAstIdentifier::from(pt.name);

        // check whether the name is in the right format
        utils::check_snake_case(&mut issues, &ident);

        // obtain the type information, must be a built-in type
        let ptype = ast_result_unwrap!(VelosiAstType::from_parse_tree(pt.ptype, st), issues);
        if !all_types && (!ptype.is_builtin() || ptype.is_flags()) {
            let msg =
                "Unsupported type. Parameter definition here only support of the built-in types.";
            let hint = "Change this type to one of [`bool`, `int`, `size`, `addr`].";
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(ptype.loc.clone())
                .build();
            issues.push(err);
        }

        let res = Self::new(ident, ptype, pt.loc);
        ast_result_return!(res, issues)
    }

    pub fn from_parse_tree_ident(
        pt: VelosiParseTreeIdentifier,
        ti: VelosiAstTypeInfo,
        _st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        let loc = pt.loc.clone();
        let ptype = VelosiAstType::new(ti, pt.loc.clone());
        let ident = VelosiAstIdentifier::from(pt);

        // check whether the name is in the right format
        utils::check_snake_case(&mut issues, &ident);

        let res = Self::new(ident, ptype, loc);
        ast_result_return!(res, issues)
    }
}

/// Implementation of [PartialEq] for [VelosiAstParam]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstParam {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident && self.ptype == other.ptype
    }
}

/// Implementation of [Hash] for [VelosiAstParam]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstParam {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ident.hash(state);
        self.ptype.hash(state);
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstParam>> for Symbol {
    fn from(c: Rc<VelosiAstParam>) -> Self {
        let n = VelosiAstNode::Param(c.clone());
        Symbol::new(c.path().clone(), c.ptype.clone(), n)
    }
}

/// Implementation of [Display] for [VelosiAstParam]
impl Display for VelosiAstParam {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}: {}", self.ident(), self.ptype)
    }
}
