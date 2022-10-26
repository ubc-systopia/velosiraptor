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

//! # VelosiAst -- Method Definitions
//!
//! This module defines the Method AST nodes of the langauge

use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use velosiparser::{VelosiParseTreeMethod, VelosiTokenStream};

use crate::ast::{
    types::VelosiAstType, VelosiAstExpr, VelosiAstIdentifier, VelosiAstNode, VelosiAstParam,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstMethod {
    /// the name of the constant
    pub ident: VelosiAstIdentifier,
    /// the return type
    pub rtype: VelosiAstType,
    /// the method parameter
    pub params: Vec<Rc<VelosiAstParam>>,
    /// a map from parameter name to the parameter
    pub params_map: HashMap<String, Rc<VelosiAstParam>>,
    /// preconditions
    pub requires: Vec<VelosiAstExpr>,
    /// method body
    pub body: Option<VelosiAstExpr>,
    /// the location of the import clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstMethod {
    pub fn new(
        ident: VelosiAstIdentifier,
        rtype: VelosiAstType,
        params: Vec<Rc<VelosiAstParam>>,
        requires: Vec<VelosiAstExpr>,
        body: Option<VelosiAstExpr>,
        loc: VelosiTokenStream,
    ) -> Self {
        let mut params_map = HashMap::new();
        params.iter().for_each(|p| {
            params_map.insert(p.ident_to_string(), p.clone());
        });
        Self {
            ident,
            rtype,
            params,
            params_map,
            requires,
            body,
            loc,
        }
    }

    pub fn ident_as_rc_string(&self) -> Rc<String> {
        self.ident.name.clone()
    }

    pub fn ident_as_str(&self) -> &str {
        self.ident.name.as_str()
    }

    pub fn ident_to_string(&self) -> String {
        self.ident.name.to_string()
    }

    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeMethod,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // create a new context in the symbol table
        st.create_context("unit".to_string());

        let name = VelosiAstIdentifier::from(pt.name);
        utils::check_snake_case(&mut issues, &name);

        // check whether the name is in the right format

        // convert all the unit parameters
        let mut params = Vec::new();
        for p in pt.params.into_iter() {
            let param = Rc::new(ast_result_unwrap!(
                VelosiAstParam::from_parse_tree(p, true, st),
                issues
            ));

            // add the param to the symbol table, if it doesn't exist already
            if let Err(e) = st.insert(param.clone().into()) {
                issues.push(e);
            } else {
                params.push(param);
            }
        }

        // obtain the type information, must be a built-in type
        let rtype = ast_result_unwrap!(VelosiAstType::from_parse_tree(pt.rettype, st), issues);
        if !rtype.is_builtin() || rtype.is_flags() {
            let msg = "Unsupported type. Function returns only support of the built-in types.";
            let hint = "Change this type to one of [`bool`, `int`, `size`, `addr`].";
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(rtype.loc.clone())
                .build();
            issues.push(err);
        }

        // convert all the unit parameters
        let mut requires = Vec::new();
        for p in pt.requires.into_iter() {
            let exp = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(p, st), issues);
            let exp = exp.into_cnf(st);
            requires.extend(exp.split_cnf());
        }

        let body = if let Some(b) = pt.body {
            Some(ast_result_unwrap!(
                VelosiAstExpr::from_parse_tree(b, st),
                issues
            ))
        } else {
            None
        };

        // restore the symbol table context
        st.drop_context();

        let res = Self::new(name, rtype, params, requires, body, pt.pos);
        ast_result_return!(res, issues)
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstMethod>> for Symbol {
    fn from(c: Rc<VelosiAstMethod>) -> Self {
        let n = VelosiAstNode::Method(c.clone());
        Symbol::new(c.ident_as_rc_string(), c.rtype.clone(), n)
    }
}

/// Implementation of [Display] for [VelosiAstMethod]
impl Display for VelosiAstMethod {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}: {}", self.ident_as_str(), self.rtype)
    }
}
