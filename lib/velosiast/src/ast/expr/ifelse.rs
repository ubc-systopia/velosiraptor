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

//! # VelosiAst - Conditional Expressions
//!
//! This module contains the definitions of the conditional (if-then-else) AST nodes

// used standard library functionality
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::{VelosiParseTreeIfElseExpr, VelosiTokenStream};

// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_unwrap, AstResult, SymbolTable};

//definitions of references AST nodes
use crate::ast::{
    VelosiAstBinOp, VelosiAstBinOpExpr, VelosiAstExpr, VelosiAstIdentLiteralExpr,
    VelosiAstTypeInfo, VelosiAstUnOp, VelosiAstUnOpExpr,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// IF Else Expression
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an boolean literal expression
#[derive(Eq, Clone)]
pub struct VelosiAstIfElseExpr {
    pub cond: Rc<VelosiAstExpr>,
    pub then: Rc<VelosiAstExpr>,
    pub other: Rc<VelosiAstExpr>,
    pub etype: VelosiAstTypeInfo,
    pub loc: VelosiTokenStream,
}

impl VelosiAstIfElseExpr {
    pub fn new(
        cond: Rc<VelosiAstExpr>,
        then: Rc<VelosiAstExpr>,
        other: Rc<VelosiAstExpr>,
        etype: VelosiAstTypeInfo,
        loc: VelosiTokenStream,
    ) -> Self {
        VelosiAstIfElseExpr {
            cond,
            then,
            other,
            etype,
            loc,
        }
    }
    pub fn from_parse_tree(
        pt: VelosiParseTreeIfElseExpr,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        let cond = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.cond, st), issues);
        let then = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.then, st), issues);
        let other = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.other, st), issues);

        let cond_type = cond.result_type();
        if *cond_type != VelosiAstTypeInfo::Bool {
            let msg = format!("Expected boolean expression was {cond_type} expression.");
            let hint = "Convert this expression into a boolean expression";

            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint.to_string())
                .add_location(cond.loc().clone())
                .build();
            issues.push(err);
        }

        let then_type = then.result_type().clone();
        let other_type = other.result_type();

        if !other_type.compatible(&then_type) {
            let msg = "The two branches of the if-then-else expression have different types";
            let hint = format!("Convert this expression into a {then_type} expression");

            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(other.loc().clone())
                .build();
            issues.push(err);
        }

        let mapping = HashMap::new();
        let e = VelosiAstIfElseExpr::new(
            Rc::new(cond),
            Rc::new(then),
            Rc::new(other),
            then_type,
            pt.loc,
        )
        .flatten(st, &mapping);
        if issues.is_ok() {
            AstResult::Ok(e)
        } else {
            AstResult::Issues(e, issues)
        }
    }

    pub fn flatten(
        self,
        st: &mut SymbolTable,
        mapping: &HashMap<Rc<String>, &VelosiAstExpr>,
    ) -> VelosiAstExpr {
        let then = Rc::new(self.then.as_ref().clone().flatten(st, mapping));
        let other = Rc::new(self.other.as_ref().clone().flatten(st, mapping));
        let cond = Rc::new(self.cond.as_ref().clone().flatten(st, mapping));

        if let VelosiAstExpr::BoolLiteral(b) = cond.as_ref() {
            if b.val {
                Rc::<VelosiAstExpr>::into_inner(then).unwrap()
            } else {
                Rc::<VelosiAstExpr>::into_inner(other).unwrap()
            }
        } else if then.result_type().is_boolean() {
            let then_expr = VelosiAstBinOpExpr::new(
                cond.clone(),
                VelosiAstBinOp::Implies,
                then,
                self.loc.clone(),
            );
            let cond_neg = VelosiAstUnOpExpr::new(VelosiAstUnOp::LNot, cond, self.loc.clone());
            let other_expr = VelosiAstBinOpExpr::new(
                Rc::new(VelosiAstExpr::UnOp(cond_neg)),
                VelosiAstBinOp::Implies,
                other,
                self.loc.clone(),
            );
            let e = VelosiAstBinOpExpr::new(
                Rc::new(VelosiAstExpr::BinOp(then_expr)),
                VelosiAstBinOp::Land,
                Rc::new(VelosiAstExpr::BinOp(other_expr)),
                self.loc,
            );
            VelosiAstExpr::BinOp(e)
        } else {
            let restype = then.result_type().clone();
            let e = VelosiAstIfElseExpr::new(cond, then, other, restype, self.loc);
            VelosiAstExpr::IfElse(e)
        }
    }

    pub fn get_interface_references(&self, irefs: &mut HashSet<Rc<String>>) {
        self.then.get_interface_references(irefs);
        self.other.get_interface_references(irefs);
        self.cond.get_interface_references(irefs);
    }

    pub fn get_state_references(&self, srefs: &mut HashSet<Rc<String>>) {
        self.then.get_state_references(srefs);
        self.other.get_state_references(srefs);
        self.cond.get_state_references(srefs);
    }

    pub fn has_state_references(&self) -> bool {
        self.then.has_state_references()
            || self.other.has_state_references()
            || self.cond.has_state_references()
    }

    pub fn has_interface_references(&self) -> bool {
        self.then.has_interface_references()
            || self.other.has_interface_references()
            || self.cond.has_interface_references()
    }

    pub fn has_var_references(&self, vars: &HashSet<&str>) -> bool {
        self.then.has_var_references(vars)
            || self.other.has_var_references(vars)
            || self.cond.has_var_references(vars)
    }

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        &self.etype
    }

    pub fn get_var_references(&self) -> HashSet<&VelosiAstIdentLiteralExpr> {
        let mut vars = self.cond.get_var_references();
        vars.extend(self.then.get_var_references());
        vars.extend(self.other.get_var_references());
        vars
    }
}

/// Implementation of [PartialEq] for [VelosiAstIfElseExpr]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstIfElseExpr {
    fn eq(&self, other: &Self) -> bool {
        self.cond == other.cond
            && self.then == other.then
            && self.other == other.other
            && self.etype == other.etype
    }
}

/// Implementation of [Hash] for [VelosiAstIfElseExpr]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstIfElseExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.cond.hash(state);
        self.then.hash(state);
        self.other.hash(state);
        self.etype.hash(state);
    }
}

impl Display for VelosiAstIfElseExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(
            format,
            "if {} {{ {} }} else {{ {} }}",
            self.cond, self.then, self.other
        )
    }
}

/// Implementation of [Debug] for [VelosiAstIfElseExpr]
impl Debug for VelosiAstIfElseExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
