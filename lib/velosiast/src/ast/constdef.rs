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

//! # VelosiAst -- Constant Definitions
//!
//! This module defines the Constant AST nodes of the langauge

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::{VelosiParseTreeConstDef, VelosiTokenStream};

// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{expr::VelosiAstExpr, types::VelosiAstType, VelosiAstIdentifier, VelosiAstNode};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Constant Definition
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Constant AST Node
///
/// This node represents a constant definition in the specification language.
#[derive(Eq, Clone)]
pub struct VelosiAstConst {
    /// the name of the constant
    pub ident: VelosiAstIdentifier,
    /// the type of the constant
    pub ctype: VelosiAstType,
    /// expression representing the value of the constnat
    pub value: VelosiAstExpr,
    /// the location of the constant definition.
    pub loc: VelosiTokenStream,
}

impl VelosiAstConst {
    /// creates a new constant definition with the given type and value
    ///
    /// # Panics
    ///
    /// The function panics if the given expression is not a constant or has a mismatched type.
    pub fn new(
        ident: VelosiAstIdentifier,
        ctype: VelosiAstType,
        value: VelosiAstExpr,
        loc: VelosiTokenStream,
    ) -> Self {
        assert!(value.is_const_expr());
        Self {
            ident,
            ctype,
            value,
            loc,
        }
    }

    /// creates a new integer constant with the given identifier and value
    pub fn new_int(ident: &str, value: u64) -> Self {
        Self::new(
            ident.into(),
            VelosiAstType::new_int(),
            VelosiAstExpr::NumLiteral(value.into()),
            VelosiTokenStream::default(),
        )
    }

    /// creates a new boolean constant with the given identifier and value
    pub fn new_bool(ident: &str, value: bool) -> Self {
        Self::new(
            ident.into(),
            VelosiAstType::new_int(),
            VelosiAstExpr::BoolLiteral(value.into()),
            VelosiTokenStream::default(),
        )
    }

    /// converts the parse tree node into an ast node, performing validity checks
    ///
    /// # Returns
    ///
    ///  - Ok, if the conversion was successful without issues
    ///  - Issues, if there were issues but the conversion still succeeded
    ///  - Err, if there were fatal errors
    ///
    pub fn from_parse_tree(
        pt: VelosiParseTreeConstDef,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convert the identifier and check whether it is in the right format
        let ident = VelosiAstIdentifier::from(pt.name);
        utils::check_upper_case(&mut issues, &ident);

        // obtain the type information, must be a built-in type
        let ctype = ast_result_unwrap!(VelosiAstType::from_parse_tree(pt.ctype, st), issues);
        if !ctype.is_builtin() || ctype.is_flags() {
            let msg = "Unsupported type. Constant definitions only support of the built-in types.";
            let hint = "Change this type to one of [`bool`, `int`, `size`, `addr`].";
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(ctype.loc.clone())
                .build();
            issues.push(err);
        }

        // obtain the value of the constant, must be a constnat expression
        let value = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(pt.value, st), issues);
        if !value.is_const_expr() {
            let msg = "Expected a constant expression.";
            let hint = "Convert this expression into a constant expression";
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(value.loc().clone())
                .build();
            issues.push(err);
        }

        // check whether the result type of the expression has a compatible type
        if !ctype.typeinfo.compatible(value.result_type()) {
            let msg = "mismatched types";
            let hint = format!(
                "expected `{}`, found `{}`",
                ctype.as_type_kind(),
                value.result_type().as_kind_str()
            );
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(value.loc().clone())
                .build();
            issues.push(err);
        }

        let res = Self {
            ident,
            ctype,
            value,
            loc: pt.loc,
        };
        ast_result_return!(res, issues)
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

    pub fn try_into_u64(&self) -> Option<u64> {
        match &self.value {
            VelosiAstExpr::NumLiteral(n) => Some(n.val),
            _ => None,
        }
    }

    pub fn try_into_bool(&self) -> Option<bool> {
        match &self.value {
            VelosiAstExpr::BoolLiteral(n) => Some(n.val),
            _ => None,
        }
    }
}

/// Implementation of [PartialEq] for [VelosiAstConst]
impl PartialEq for VelosiAstConst {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident && self.ctype == other.ctype && self.value == other.value
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstConst>> for Symbol {
    fn from(c: Rc<VelosiAstConst>) -> Self {
        let n = VelosiAstNode::Const(c.clone());
        Symbol::new(c.path().clone(), c.ctype.clone(), n)
    }
}

/// Implementation of [Display] for [VelosiAstConst]
impl Display for VelosiAstConst {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "const {} : {} = {};",
            self.ident(),
            self.ctype,
            self.value
        )
    }
}

/// Implementation of [Debug] for [VelosiAstConst]
impl Debug for VelosiAstConst {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
