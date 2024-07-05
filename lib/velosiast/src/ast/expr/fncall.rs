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

//! # VelosiAst - Function Call Expressions
//!
//! This module contains the definitions of the function call AST nodes

// used standard library functionality
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeFnCallExpr;
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{
    VelosiAstExpr, VelosiAstIdentLiteralExpr, VelosiAstIdentifier, VelosiAstNode, VelosiAstTypeInfo,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Function Call Expression
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an boolean literal expression
#[derive(Eq, Clone)]
pub struct VelosiAstFnCallExpr {
    pub ident: VelosiAstIdentifier,
    pub args: Vec<Rc<VelosiAstExpr>>,
    pub etype: VelosiAstTypeInfo,
    pub loc: VelosiTokenStream,
}

impl VelosiAstFnCallExpr {
    pub fn new(ident: VelosiAstIdentifier, etype: VelosiAstTypeInfo) -> Self {
        Self::with_loc(ident, etype, VelosiTokenStream::default())
    }

    pub fn with_loc(
        ident: VelosiAstIdentifier,
        etype: VelosiAstTypeInfo,
        loc: VelosiTokenStream,
    ) -> Self {
        VelosiAstFnCallExpr {
            ident,
            args: Vec::new(),
            etype,
            loc,
        }
    }

    pub fn push_arg(&mut self, arg: Rc<VelosiAstExpr>) -> &mut Self {
        self.args.push(arg);
        self
    }

    pub fn add_args(&mut self, args: Vec<Rc<VelosiAstExpr>>) -> &mut Self {
        self.args.extend(args);
        self
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeFnCallExpr,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();
        let e = ast_result_unwrap!(Self::from_parse_tree_raw(pt, st), issues);
        let mappings = HashMap::new();
        ast_result_return!(e.flatten(st, &mappings), issues)
    }

    pub fn from_parse_tree_raw(
        pt: VelosiParseTreeFnCallExpr,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // process the function call arguments
        let mut args = Vec::with_capacity(pt.args.len());
        for a in pt.args.into_iter() {
            let arg = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(a, st), issues);
            args.push(Rc::new(arg));
        }

        // construct the default function call expression node
        let mut res = VelosiAstFnCallExpr {
            ident: VelosiAstIdentifier::from(pt.name),
            args,
            etype: VelosiAstTypeInfo::Integer,
            loc: pt.loc,
        };

        let fn_sym = st.lookup(res.path());
        if fn_sym.is_none() {
            // there was no symbol
            let err = VelosiAstErrUndef::new(res.path().clone(), res.loc.clone());
            return AstResult::Issues(res, err.into());
        }

        let fn_sym = fn_sym.unwrap();
        match &fn_sym.ast_node {
            VelosiAstNode::Method(m) => {
                utils::check_fn_call_args(
                    &mut issues,
                    st,
                    m.params.as_slice(),
                    res.args.as_slice(),
                    &res.loc,
                );
                res.etype = m.rtype.typeinfo.clone();
            }
            VelosiAstNode::Unit(u) => {
                utils::check_fn_call_args(
                    &mut issues,
                    st,
                    u.params_as_slice(),
                    res.args.as_slice(),
                    &res.loc,
                );
                if u.is_abstract() {
                    // cannot call abstract units.
                    let msg = "attempted to instantiate abstract unit";
                    let hint = "make this unit concrete by removing the `abstract` modifier.";
                    let err = VelosiAstErrBuilder::err(msg.to_string())
                        .add_location(res.loc.clone())
                        .add_related_location(
                            hint.to_string(),
                            u.loc().from_self_with_subrange(0..2),
                        )
                        .build();
                    issues.push(err);
                }

                res.etype = VelosiAstTypeInfo::TypeRef(u.ident().clone());
            }
            _ => {
                // we have the wrong kind of symbol
                let err = VelosiAstErrUndef::with_other(
                    res.ident().clone(),
                    res.loc.clone(),
                    fn_sym.loc().clone(),
                );
                issues.push(err.into());
            }
        }

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

    pub fn flatten(
        self,
        st: &mut SymbolTable,
        mapping: &HashMap<Rc<String>, &VelosiAstExpr>,
    ) -> VelosiAstExpr {
        let mut res = self;
        res.args = res
            .args
            .into_iter()
            .map(|a| Rc::new(a.as_ref().clone().flatten(st, mapping)))
            .collect();

        let fn_sym = st.lookup(res.path());
        if fn_sym.is_none() {
            return VelosiAstExpr::FnCall(res);
        }

        let fn_sym = fn_sym.unwrap();
        match &fn_sym.ast_node {
            VelosiAstNode::Method(m) => {
                if let Some(body) = &m.body {
                    // we have a body we can rewrite, gather all the arguments
                    let mut mapping = HashMap::new();
                    for (i, p) in m.params.iter().enumerate() {
                        mapping.insert(p.ident().clone(), res.args[i].as_ref());
                    }
                    body.as_ref().clone().flatten(st, &mapping)
                } else {
                    VelosiAstExpr::FnCall(res)
                }
            }
            _ => VelosiAstExpr::FnCall(res),
        }
    }

    pub fn flatten_raw(
        self,
        st: &mut SymbolTable,
        mapping: &HashMap<Rc<String>, &VelosiAstExpr>,
    ) -> Self {
        let mut res = self;
        res.args = res
            .args
            .into_iter()
            .map(|a| Rc::new(a.as_ref().clone().flatten(st, mapping)))
            .collect();
        res
    }

    pub fn get_interface_references(&self, irefs: &mut HashSet<Rc<String>>) {
        for a in self.args.iter() {
            a.get_interface_references(irefs);
        }
    }

    pub fn get_state_references(&self, srefs: &mut HashSet<Rc<String>>) {
        for a in self.args.iter() {
            a.get_state_references(srefs);
        }
    }

    pub fn has_state_references(&self) -> bool {
        self.args.iter().any(|a| a.has_state_references())
    }

    pub fn has_interface_references(&self) -> bool {
        self.args.iter().any(|a| a.has_interface_references())
    }

    pub fn has_var_references(&self, vars: &HashSet<&str>) -> bool {
        self.args.iter().any(|a| a.has_var_references(vars))
    }

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        &self.etype
    }

    pub fn get_var_references(&self) -> HashSet<&VelosiAstIdentLiteralExpr> {
        HashSet::new()

        // unimplemented!();
    }

    pub fn has_translate_range(&self) -> bool {
        self.ident().contains("translate.range")
            || self.args.iter().any(|a| a.has_translate_range())
    }
}

/// Implementation of [PartialEq] for [VelosiAstFnCallExpr]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstFnCallExpr {
    fn eq(&self, other: &Self) -> bool {
        // TODO: what does make sens here?
        self.ident == other.ident && self.args == other.args && self.etype == other.etype
    }
}

/// Implementation of [Hash] for [VelosiAstFnCallExpr]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstFnCallExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ident.hash(state);
        self.args.hash(state);
        self.etype.hash(state);
    }
}

impl Display for VelosiAstFnCallExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}(", self.ident())?;
        for (i, p) in self.args.iter().enumerate() {
            if i != 0 {
                write!(format, ", ")?;
            }
            write!(format, "{p}")?;
        }
        write!(format, ")")
    }
}

/// Implementation of [Debug] for [VelosiAstFnCallExpr]
impl Debug for VelosiAstFnCallExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
