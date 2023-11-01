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

//! # VelosiAst - Unary Operation Expressions
//!
//! This module contains the definitions of the unary operation AST nodes.

// used standard library functionality
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::{VelosiParseTreeUnOp, VelosiParseTreeUnOpExpr};
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_unwrap, AstResult, SymbolTable};

use crate::ast::{
    VelosiAstBoolLiteralExpr, VelosiAstExpr, VelosiAstIdentLiteralExpr, VelosiAstNumLiteralExpr,
    VelosiAstTypeInfo,
};

///////////////////////////////////////////////////////////////////////////////////////////////////
// Unary Operation Expressions
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an unary operator
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub enum VelosiAstUnOp {
    // arithmetic operators
    Not,
    // Ref,
    // boolean operator
    LNot,
}

/// Implementation of an unary operator
impl VelosiAstUnOp {
    pub fn types_ok(&self, expr_type: &VelosiAstTypeInfo) -> bool {
        use VelosiAstUnOp::*;
        match self {
            Not => expr_type.compatible(&VelosiAstTypeInfo::Integer),
            LNot => expr_type.compatible(&VelosiAstTypeInfo::Bool),
        }
    }

    pub fn is_arithmetic(&self) -> bool {
        use VelosiAstUnOp::*;
        matches!(self, Not)
    }

    pub fn is_logical(&self) -> bool {
        use VelosiAstUnOp::*;
        matches!(self, LNot)
    }

    /// the result type of a binary operation
    pub fn result_numeric(&self) -> bool {
        self.is_arithmetic()
    }

    /// the result type of a binary operation
    pub fn result_boolean(&self) -> bool {
        self.is_logical()
    }

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        use self::VelosiAstUnOp::*;
        match self {
            Not => &VelosiAstTypeInfo::Integer,
            LNot => &VelosiAstTypeInfo::Bool,
            // Ref => panic!("not supported"),
        }
    }
}

/// Implementation of [Display] for [VelosiAstUnOp]
impl Display for VelosiAstUnOp {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        use self::VelosiAstUnOp::*;
        match self {
            Not => write!(format, "~"),
            LNot => write!(format, "!"),
            //Ref => write!(format, "&"),
        }
    }
}

/// Implementation of [Debug] for [VelosiAstUnOp]
impl Debug for VelosiAstUnOp {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

impl From<VelosiParseTreeUnOp> for VelosiAstUnOp {
    fn from(op: VelosiParseTreeUnOp) -> VelosiAstUnOp {
        use VelosiParseTreeUnOp::*;
        match op {
            Not => VelosiAstUnOp::Not,
            LNot => VelosiAstUnOp::LNot,
            // Ref => VelosiAstUnOp::Ref,
        }
    }
}

/// Represents an unary operation
#[derive(Eq, Clone)]
pub struct VelosiAstUnOpExpr {
    pub op: VelosiAstUnOp,
    pub expr: Rc<VelosiAstExpr>,
    pub loc: VelosiTokenStream,
}

impl VelosiAstUnOpExpr {
    pub fn new(
        op: VelosiAstUnOp,
        expr: Rc<VelosiAstExpr>,
        loc: VelosiTokenStream,
    ) -> VelosiAstUnOpExpr {
        VelosiAstUnOpExpr { op, expr, loc }
    }

    pub fn new_lnot(expr: Rc<VelosiAstExpr>) -> VelosiAstExpr {
        let loc = expr.loc().clone();
        VelosiAstExpr::UnOp(VelosiAstUnOpExpr::new(VelosiAstUnOp::LNot, expr, loc))
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeUnOpExpr,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convet the lhs/rhs and operator
        let op = VelosiAstUnOp::from(pt.op);
        let expr = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.expr, st), issues);

        // obtain the result types
        let expr_type = expr.result_type();

        // evaluate whether the types are ok
        if !op.types_ok(expr_type) {
            let msg = "Unsupported type combination in unary operation";
            let hint = format!("No implementation for `{op} {expr_type}`");

            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.clone())
                .build();
            issues.push(err);
        }

        // evaluate the expression, see if we can fold the constants
        let res = VelosiAstUnOpExpr::new(op, Rc::new(expr), pt.loc).eval();

        if issues.is_ok() {
            AstResult::Ok(res)
        } else {
            AstResult::Issues(res, issues)
        }
    }

    fn eval(self) -> VelosiAstExpr {
        use VelosiAstExpr::*;
        use VelosiAstUnOp::*;
        match (self.op, self.expr.as_ref()) {
            // arithmetic operators
            (Not, NumLiteral(l)) => NumLiteral(VelosiAstNumLiteralExpr::with_loc(!l.val, self.loc)),
            // boolean operators
            (LNot, BoolLiteral(l)) => BoolLiteral(VelosiAstBoolLiteralExpr::new(!l.val, self.loc)),
            _ => UnOp(self),
        }
    }

    pub fn flatten(
        self,
        st: &mut SymbolTable,
        mapping: &HashMap<Rc<String>, &VelosiAstExpr>,
    ) -> VelosiAstExpr {
        match self.expr.as_ref().clone().flatten(st, mapping) {
            // the other expression is also an unary operation
            VelosiAstExpr::UnOp(e) => {
                // if the two unary opearations are the same, we can apply the double rule
                if self.op == e.op {
                    e.expr.as_ref().clone()
                } else {
                    VelosiAstUnOpExpr::new(self.op, Rc::new(VelosiAstExpr::UnOp(e)), self.loc)
                        .eval()
                }
            }
            // the other expression is not unary, evaluate and return
            e => VelosiAstUnOpExpr::new(self.op, Rc::new(e), self.loc).eval(),
        }
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

    pub fn has_interface_references(&self) -> bool {
        self.expr.has_interface_references()
    }

    pub fn has_var_references(&self, vars: &HashSet<&str>) -> bool {
        self.expr.has_var_references(vars)
    }

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        self.op.result_type()
    }

    pub fn get_var_references(&self) -> HashSet<&VelosiAstIdentLiteralExpr> {
        self.expr.get_var_references()
    }
}

/// Implementation of [PartialEq] for [VelosiAstUnOpExpr]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstUnOpExpr {
    fn eq(&self, other: &Self) -> bool {
        self.op == other.op && self.expr == other.expr
    }
}

/// Implementation of [Hash] for [VelosiAstUnOpExpr]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstUnOpExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.op.hash(state);
        self.expr.hash(state);
    }
}

impl Display for VelosiAstUnOpExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}({})", self.op, self.expr)
    }
}

/// Implementation of [Debug] for [VelosiAstUnOpExpr]
impl Debug for VelosiAstUnOpExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
