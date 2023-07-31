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

//! # VelosiAst - Quantifier Expressions
//!
//! This module contains the definitions of the quantifier (forall, exists) AST nodes

// used standard library functionality
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::{VelosiParseTreeQuantifier, VelosiParseTreeQuantifierExpr, VelosiTokenStream};

// used crate functionality
use crate::error::VelosiAstIssues;
use crate::{ast_result_return, ast_result_unwrap, AstResult, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{VelosiAstExpr, VelosiAstIdentLiteralExpr, VelosiAstParam};

///////////////////////////////////////////////////////////////////////////////////////////////////
// Quantifier Expression
///////////////////////////////////////////////////////////////////////////////////////////////////

/// representation of a quantifier
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub enum VelosiAstQuantifier {
    Forall,
    Exists,
}

/// Implementation of [From] for [VelosiAstQuantifier]
impl From<VelosiParseTreeQuantifier> for VelosiAstQuantifier {
    fn from(op: VelosiParseTreeQuantifier) -> VelosiAstQuantifier {
        use VelosiParseTreeQuantifier::*;
        match op {
            Forall => VelosiAstQuantifier::Forall,
            Exists => VelosiAstQuantifier::Exists,
        }
    }
}

/// Implementation of [Display] for [VelosiAstQuantifier]
impl Display for VelosiAstQuantifier {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        use VelosiAstQuantifier::*;
        match self {
            Forall => write!(format, "forall"),
            Exists => write!(format, "exists"),
        }
    }
}

/// Implementation of [Debug] for [VelosiAstQuantifier]
impl Debug for VelosiAstQuantifier {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Represents an unary operation
#[derive(Eq, Clone)]
pub struct VelosiAstQuantifierExpr {
    pub quant: VelosiAstQuantifier,
    pub params: Vec<Rc<VelosiAstParam>>,
    pub expr: Rc<VelosiAstExpr>,
    pub loc: VelosiTokenStream,
}

impl VelosiAstQuantifierExpr {
    pub fn new(
        quant: VelosiAstQuantifier,
        params: Vec<Rc<VelosiAstParam>>,
        expr: Rc<VelosiAstExpr>,
        loc: VelosiTokenStream,
    ) -> VelosiAstQuantifierExpr {
        VelosiAstQuantifierExpr {
            quant,
            params,
            expr,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeQuantifierExpr,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        st.create_context("quantifier".to_string());

        let quant = VelosiAstQuantifier::from(pt.quant);

        let mut params = Vec::new();
        for p in pt.params {
            let param = Rc::new(ast_result_unwrap!(
                VelosiAstParam::from_parse_tree(p, false, st),
                issues
            ));

            // add the param to the symbol table, if it doesn't exist already
            if let Err(e) = st.insert(param.clone().into()) {
                issues.push(*e);
            } else {
                params.push(param);
            }
        }

        let expr = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.expr, st), issues);

        st.drop_context();

        let e = VelosiAstQuantifierExpr::new(quant, params, Rc::new(expr), pt.loc);
        ast_result_return!(VelosiAstExpr::Quantifier(e), issues)
    }

    pub fn flatten(
        self,
        _st: &mut SymbolTable,
        _mapping: &HashMap<Rc<String>, &VelosiAstExpr>,
    ) -> VelosiAstExpr {
        panic!("nyi");
    }

    pub fn get_interface_references(&self, irefs: &mut HashSet<Rc<String>>) {
        self.expr.get_interface_references(irefs);
    }

    pub fn get_state_references(&self, srefs: &mut HashSet<Rc<String>>) {
        self.expr.get_state_references(srefs);
    }

    pub fn has_state_references(&self) -> bool {
        self.expr.has_state_references()
    }

    pub fn has_var_references(&self, _vars: &HashSet<&str>) -> bool {
        unimplemented!("should check the quantifier variables and remove them!\n");
        // self.expr.has_var_references(vars)
    }

    pub fn has_interface_references(&self) -> bool {
        self.expr.has_interface_references()
    }

    pub fn get_var_references(&self) -> HashSet<&VelosiAstIdentLiteralExpr> {
        unimplemented!();
    }
}

/// Implementation of [PartialEq] for [VelosiAstQuantifierExpr]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstQuantifierExpr {
    fn eq(&self, other: &Self) -> bool {
        self.quant == other.quant && self.params == other.params && self.expr == other.expr
    }
}

/// Implementation of [Hash] for [VelosiAstQuantifierExpr]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstQuantifierExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.quant.hash(state);
        self.params.hash(state);
        self.expr.hash(state);
    }
}

/// Implementation of [Display] for [VelosiParseTreeQuantifierExpr]
impl Display for VelosiAstQuantifierExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "({} |", self.quant)?;
        // for (i, p) in self.params.iter().enumerate() {
        //     if i != 0 {
        //         write!(format, ", ")?;
        //     }
        //     write!(format, "{}", p)?;
        // }
        write!(format, " :: {})", self.expr)
    }
}

/// Implementation of [Debug] for [VelosiAstQuantifierExpr]
impl Debug for VelosiAstQuantifierExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
