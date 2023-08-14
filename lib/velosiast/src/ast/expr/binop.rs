// Velosiraptor AST
//
//
// MIT License
//
// Copyright (c) 2021-2023 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiAst - Binary Operation Expressions
//!
//! This module contains the definitions of the binary operation AST nodes.

// used standard library functionality
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::{VelosiParseTreeBinOp, VelosiParseTreeBinOpExpr};
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_unwrap, AstResult, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{
    VelosiAstBoolLiteralExpr, VelosiAstExpr, VelosiAstIdentLiteralExpr, VelosiAstNumLiteralExpr,
    VelosiAstTypeInfo,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Binary Operations
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Binary operations for [VelosiAstExpr] <OP> [VelosiAstExpr]
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub enum VelosiAstBinOp {
    // arithmetic opreators: Numeric <OP> Numeric -> Numeric
    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
    LShift,
    RShift,
    And,
    Xor,
    Or,
    // equality operators: Numeric|Bool <OP> Numeric|Bool -> Bool
    Eq,
    Ne,
    // Comparison Operators: Numeric <OP> Numeric -> Bool
    Lt,
    Gt,
    Le,
    Ge,
    // logical operators: Bool <OP> Bool -> Bool
    Land,
    Lor,
    Implies,
}

/// Implementation of binary operators
impl VelosiAstBinOp {
    pub fn types_ok(&self, lhs_type: &VelosiAstTypeInfo, rhs_type: &VelosiAstTypeInfo) -> bool {
        use VelosiAstBinOp::*;
        match self {
            Plus | Minus | Multiply | Divide | Modulo | LShift | RShift | And | Xor | Or => {
                lhs_type.compatible(&VelosiAstTypeInfo::Integer)
                    && rhs_type.compatible(&VelosiAstTypeInfo::Integer)
            }
            Eq | Ne => rhs_type.compatible(lhs_type),
            Lt | Gt | Le | Ge => {
                lhs_type.compatible(&VelosiAstTypeInfo::Integer)
                    && rhs_type.compatible(&VelosiAstTypeInfo::Integer)
            }
            Land | Lor | Implies => {
                lhs_type.compatible(&VelosiAstTypeInfo::Bool)
                    && rhs_type.compatible(&VelosiAstTypeInfo::Bool)
            }
        }
    }

    pub fn is_arithmetic(&self) -> bool {
        use VelosiAstBinOp::*;
        matches!(
            self,
            Plus | Minus | Multiply | Divide | Modulo | LShift | RShift | And | Xor | Or
        )
    }

    pub fn is_equality(&self) -> bool {
        use VelosiAstBinOp::*;
        matches!(self, Eq | Ne)
    }

    pub fn is_comparison(&self) -> bool {
        use VelosiAstBinOp::*;
        matches!(self, Lt | Gt | Le | Ge)
    }

    pub fn is_logical(&self) -> bool {
        use VelosiAstBinOp::*;
        matches!(self, Land | Lor | Implies)
    }

    /// the result type of a binary operation
    fn result_numeric(&self) -> bool {
        use VelosiAstBinOp::*;
        match self {
            // arithmetic opreators
            Plus => true,
            Minus => true,
            Multiply => true,
            Divide => true,
            Modulo => true,
            LShift => true,
            RShift => true,
            And => true,
            Xor => true,
            Or => true,
            // boolean operators
            Eq => false,
            Ne => false,
            Lt => false,
            Gt => false,
            Le => false,
            Ge => false,
            Land => false,
            Lor => false,
            Implies => false,
        }
    }

    /// the result type of a binary operation
    fn result_boolean(&self) -> bool {
        use VelosiAstBinOp::*;
        match self {
            // arithmetic opreators
            Plus => false,
            Minus => false,
            Multiply => false,
            Divide => false,
            Modulo => false,
            LShift => false,
            RShift => false,
            And => false,
            Xor => false,
            Or => false,
            // boolean operators
            Eq => true,
            Ne => true,
            Lt => true,
            Gt => true,
            Le => true,
            Ge => true,
            Land => true,
            Lor => true,
            Implies => true,
        }
    }

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        if self.result_numeric() {
            &VelosiAstTypeInfo::Integer
        } else if self.result_boolean() {
            &VelosiAstTypeInfo::Bool
        } else {
            unreachable!()
        }
    }
}

/// Implementation of [Display] for [VelosiAstBinOp]
impl Display for VelosiAstBinOp {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        use VelosiAstBinOp::*;
        match self {
            Plus => write!(format, "+"),
            Minus => write!(format, "-"),
            Multiply => write!(format, "*"),
            Divide => write!(format, "/"),
            Modulo => write!(format, "%"),
            LShift => write!(format, "<<"),
            RShift => write!(format, ">>"),
            And => write!(format, "&"),
            Xor => write!(format, "^"),
            Or => write!(format, "|"),
            Eq => write!(format, "=="),
            Ne => write!(format, "!="),
            Lt => write!(format, "<"),
            Gt => write!(format, ">"),
            Le => write!(format, "<="),
            Ge => write!(format, ">="),
            Land => write!(format, "&&"),
            Lor => write!(format, "||"),
            Implies => write!(format, "==>"),
        }
    }
}

/// Implementation of [Debug] for [VelosiAstBinOp]
impl Debug for VelosiAstBinOp {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Convert the parse tree binop to a ast binop
impl From<VelosiParseTreeBinOp> for VelosiAstBinOp {
    fn from(op: VelosiParseTreeBinOp) -> VelosiAstBinOp {
        use VelosiParseTreeBinOp::*;
        match op {
            Plus => VelosiAstBinOp::Plus,
            Minus => VelosiAstBinOp::Minus,
            Multiply => VelosiAstBinOp::Multiply,
            Divide => VelosiAstBinOp::Divide,
            Modulo => VelosiAstBinOp::Modulo,
            LShift => VelosiAstBinOp::LShift,
            RShift => VelosiAstBinOp::RShift,
            And => VelosiAstBinOp::And,
            Xor => VelosiAstBinOp::Xor,
            Or => VelosiAstBinOp::Or,
            Eq => VelosiAstBinOp::Eq,
            Ne => VelosiAstBinOp::Ne,
            Lt => VelosiAstBinOp::Lt,
            Gt => VelosiAstBinOp::Gt,
            Le => VelosiAstBinOp::Le,
            Ge => VelosiAstBinOp::Ge,
            Land => VelosiAstBinOp::Land,
            Lor => VelosiAstBinOp::Lor,
            Implies => VelosiAstBinOp::Implies,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Binary Operation Expression
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents a binary operation `expr <op> expr`
#[derive(Eq, Clone)]
pub struct VelosiAstBinOpExpr {
    pub lhs: Rc<VelosiAstExpr>,
    pub op: VelosiAstBinOp,
    pub rhs: Rc<VelosiAstExpr>,
    pub loc: VelosiTokenStream,
}

impl VelosiAstBinOpExpr {
    pub fn new(
        lhs: Rc<VelosiAstExpr>,
        op: VelosiAstBinOp,
        rhs: Rc<VelosiAstExpr>,
        loc: VelosiTokenStream,
    ) -> VelosiAstBinOpExpr {
        VelosiAstBinOpExpr { lhs, op, rhs, loc }
    }

    pub fn land(lhs: Rc<VelosiAstExpr>, rhs: Rc<VelosiAstExpr>) -> Self {
        Self::new(lhs, VelosiAstBinOp::Land, rhs, Default::default())
    }

    pub fn lor(lhs: Rc<VelosiAstExpr>, rhs: Rc<VelosiAstExpr>) -> Self {
        Self::new(lhs, VelosiAstBinOp::Lor, rhs, Default::default())
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeBinOpExpr,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convet the lhs/rhs and operator
        let op = VelosiAstBinOp::from(pt.op);
        let lhs = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.lhs, st), issues);
        let rhs = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.rhs, st), issues);

        // obtain the result types
        let lhs_type = lhs.result_type();
        let rhs_type = rhs.result_type();

        // evaluate whether the types are ok
        if !op.types_ok(lhs_type, rhs_type) {
            let msg = "Unsupported type combination in binary operation";
            let hint = format!("No implementation for `{lhs_type} {op} {rhs_type}`");

            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.clone())
                .build();
            issues.push(err);
        }

        // evaluate the expression, see if we can fold the constants
        let res = VelosiAstBinOpExpr::new(Rc::new(lhs), op, Rc::new(rhs), pt.loc)
            .canonicalize()
            .eval();

        if issues.is_ok() {
            AstResult::Ok(res)
        } else {
            AstResult::Issues(res, issues)
        }
    }

    fn canonicalize(self) -> Self {
        let VelosiAstBinOpExpr { lhs, op, rhs, loc } = self;
        let (lhs, op, rhs) = match (lhs, op, rhs) {
            (lhs, VelosiAstBinOp::Plus, rhs) => {
                if lhs <= rhs {
                    (lhs, op, rhs)
                } else {
                    (rhs, op, lhs)
                }
            }
            (lhs, VelosiAstBinOp::Multiply, rhs) => {
                if lhs <= rhs {
                    (lhs, op, rhs)
                } else {
                    (rhs, op, lhs)
                }
            }
            (lhs, VelosiAstBinOp::And, rhs) => {
                if lhs <= rhs {
                    (lhs, op, rhs)
                } else {
                    (rhs, op, lhs)
                }
            }
            (lhs, VelosiAstBinOp::Or, rhs) => {
                if lhs <= rhs {
                    (lhs, op, rhs)
                } else {
                    (rhs, op, lhs)
                }
            }
            (lhs, VelosiAstBinOp::Xor, rhs) => {
                if lhs <= rhs {
                    (lhs, op, rhs)
                } else {
                    (rhs, op, lhs)
                }
            }
            (lhs, VelosiAstBinOp::Eq, rhs) => {
                if lhs <= rhs {
                    (lhs, op, rhs)
                } else {
                    (rhs, op, lhs)
                }
            }
            (lhs, VelosiAstBinOp::Ne, rhs) => {
                if lhs <= rhs {
                    (lhs, op, rhs)
                } else {
                    (rhs, op, lhs)
                }
            }
            (lhs, VelosiAstBinOp::Gt, rhs) => {
                // lhs > rhs => rhs < lhs
                (rhs, VelosiAstBinOp::Lt, lhs)
            }
            (lhs, VelosiAstBinOp::Ge, rhs) => {
                // lhs >= rhs => rhs <= lhs
                (rhs, VelosiAstBinOp::Le, lhs)
            }
            (lhs, VelosiAstBinOp::Land, rhs) => {
                if lhs <= rhs {
                    (lhs, op, rhs)
                } else {
                    (rhs, op, lhs)
                }
            }
            (lhs, VelosiAstBinOp::Lor, rhs) => {
                if lhs <= rhs {
                    (lhs, op, rhs)
                } else {
                    (rhs, op, lhs)
                }
            }

            (lhs, op, rhs) => (lhs, op, rhs),
        };

        // we no know that the constants are moved to the right.
        let (lhs, op, rhs) = if rhs.is_const_expr() {
            if let VelosiAstExpr::BinOp(lhs_expr) = lhs.as_ref() {
                if lhs_expr.rhs.is_const_expr() {
                    use VelosiAstBinOp::*;
                    match (lhs_expr.op, op) {
                        (Plus, Plus)
                        | (Multiply, Multiply)
                        | (And, And)
                        | (Or, Or)
                        | (Xor, Xor)
                        | (Eq, Eq)
                        | (Land, Land)
                        | (Lor, Lor) => {
                            // we can fold the constants
                            let lhs = &lhs_expr.lhs;
                            let rhs =
                                VelosiAstBinOpExpr::new(lhs_expr.rhs.clone(), op, rhs, loc.clone())
                                    .eval();
                            (lhs.clone(), op, Rc::new(rhs))
                        }
                        (Minus, Minus) => {
                            // (a - b) - c => a - (b + c)
                            let lhs = &lhs_expr.lhs;
                            let rhs = VelosiAstBinOpExpr::new(
                                lhs_expr.rhs.clone(),
                                Plus,
                                rhs,
                                loc.clone(),
                            )
                            .eval();
                            (lhs.clone(), op, Rc::new(rhs))
                        }
                        (Divide, Divide) => {
                            // (a / b) / c => a / (b * c)
                            let lhs = &lhs_expr.lhs;
                            let rhs = VelosiAstBinOpExpr::new(
                                lhs_expr.rhs.clone(),
                                Multiply,
                                rhs,
                                loc.clone(),
                            )
                            .eval();
                            (lhs.clone(), op, Rc::new(rhs))
                        }
                        (LShift, LShift) => {
                            // (a << b) << c => a << (b + c)
                            let lhs = &lhs_expr.lhs;
                            let rhs = VelosiAstBinOpExpr::new(
                                lhs_expr.rhs.clone(),
                                Plus,
                                rhs,
                                loc.clone(),
                            )
                            .eval();
                            (lhs.clone(), op, Rc::new(rhs))
                        }
                        (RShift, RShift) => {
                            // (a >> b) >> c => a >> (b + c)
                            let lhs = &lhs_expr.lhs;
                            let rhs = VelosiAstBinOpExpr::new(
                                lhs_expr.rhs.clone(),
                                Plus,
                                rhs,
                                loc.clone(),
                            )
                            .eval();
                            (lhs.clone(), op, Rc::new(rhs))
                        }
                        (LShift, RShift) => {
                            if lhs_expr.rhs.const_expr_result_num().unwrap()
                                >= rhs.const_expr_result_num().unwrap()
                            {
                                // (a << b) >> c => a << (b - c)
                                let lhs = &lhs_expr.lhs;
                                let rhs = VelosiAstBinOpExpr::new(
                                    lhs_expr.rhs.clone(),
                                    Minus,
                                    rhs,
                                    loc.clone(),
                                )
                                .eval();
                                let op = LShift;
                                (lhs.clone(), op, Rc::new(rhs))
                            } else {
                                // (a << b) >> c => a >> (c - b)
                                let lhs = &lhs_expr.lhs;
                                let rhs = VelosiAstBinOpExpr::new(
                                    rhs,
                                    Minus,
                                    lhs_expr.rhs.clone(),
                                    loc.clone(),
                                )
                                .eval();
                                let op = RShift;
                                (lhs.clone(), op, Rc::new(rhs))
                            }
                        }
                        (RShift, LShift) => {
                            if lhs_expr.rhs.const_expr_result_num().unwrap()
                                >= rhs.const_expr_result_num().unwrap()
                            {
                                // (a >> b) << c => a >> (b - c)
                                let lhs = &lhs_expr.lhs;
                                let rhs = VelosiAstBinOpExpr::new(
                                    lhs_expr.rhs.clone(),
                                    Minus,
                                    rhs,
                                    loc.clone(),
                                )
                                .eval();
                                let op = LShift;
                                (lhs.clone(), op, Rc::new(rhs))
                            } else {
                                // (a >> b) << c => a << (c - b)
                                let lhs = &lhs_expr.lhs;
                                let rhs = VelosiAstBinOpExpr::new(
                                    rhs,
                                    Minus,
                                    lhs_expr.rhs.clone(),
                                    loc.clone(),
                                )
                                .eval();
                                let op = RShift;
                                (lhs.clone(), op, Rc::new(rhs))
                            }
                        }
                        _ => (Rc::new(VelosiAstExpr::BinOp(lhs_expr.clone())), op, rhs),
                    }
                } else {
                    (Rc::new(VelosiAstExpr::BinOp(lhs_expr.clone())), op, rhs)
                }
            } else {
                (lhs, op, rhs)
            }
        } else {
            (lhs, op, rhs)
        };

        VelosiAstBinOpExpr { lhs, op, rhs, loc }
    }

    fn eval(self) -> VelosiAstExpr {
        use VelosiAstBinOp::*;
        use VelosiAstExpr::*;
        match (self.lhs.as_ref(), self.op, self.rhs.as_ref()) {
            // arithmetic operators
            (NumLiteral(l), Plus, NumLiteral(r)) => {
                // TODO: check for overflow!
                NumLiteral(VelosiAstNumLiteralExpr::new(l.val + r.val, self.loc))
            }
            (NumLiteral(l), Minus, NumLiteral(r)) => {
                // TODO: check for underflow!
                NumLiteral(VelosiAstNumLiteralExpr::new(l.val - r.val, self.loc))
            }
            (NumLiteral(l), Multiply, NumLiteral(r)) => {
                // TODO: check for overflow
                NumLiteral(VelosiAstNumLiteralExpr::new(l.val * r.val, self.loc))
            }
            (NumLiteral(l), Divide, NumLiteral(r)) => {
                // TODO: check for division by 0
                NumLiteral(VelosiAstNumLiteralExpr::new(l.val / r.val, self.loc))
            }
            (NumLiteral(l), Modulo, NumLiteral(r)) => {
                // TODO: check for division by 0!
                NumLiteral(VelosiAstNumLiteralExpr::new(l.val % r.val, self.loc))
            }
            (NumLiteral(l), LShift, NumLiteral(r)) => {
                // TODO: check for shift amount
                NumLiteral(VelosiAstNumLiteralExpr::new(l.val << r.val, self.loc))
            }
            (NumLiteral(l), RShift, NumLiteral(r)) => {
                // TODO: check for shift amount!
                NumLiteral(VelosiAstNumLiteralExpr::new(l.val >> r.val, self.loc))
            }
            (NumLiteral(l), And, NumLiteral(r)) => {
                // TODO: check for shift amount!
                NumLiteral(VelosiAstNumLiteralExpr::new(l.val & r.val, self.loc))
            }
            (NumLiteral(l), Or, NumLiteral(r)) => {
                // TODO: check for shift amount!
                NumLiteral(VelosiAstNumLiteralExpr::new(l.val | r.val, self.loc))
            }
            (NumLiteral(l), Xor, NumLiteral(r)) => {
                // TODO: check for shift amount!
                NumLiteral(VelosiAstNumLiteralExpr::new(l.val ^ r.val, self.loc))
            }
            // equality operators
            (NumLiteral(l), Eq, NumLiteral(r)) => {
                BoolLiteral(VelosiAstBoolLiteralExpr::new(l.val == r.val, self.loc))
            }
            (NumLiteral(l), Ne, NumLiteral(r)) => {
                BoolLiteral(VelosiAstBoolLiteralExpr::new(l.val != r.val, self.loc))
            }
            (BoolLiteral(l), Eq, BoolLiteral(r)) => {
                BoolLiteral(VelosiAstBoolLiteralExpr::new(l.val == r.val, self.loc))
            }
            (BoolLiteral(l), Ne, BoolLiteral(r)) => {
                BoolLiteral(VelosiAstBoolLiteralExpr::new(l.val != r.val, self.loc))
            }
            // comparison operators
            (NumLiteral(l), Lt, NumLiteral(r)) => {
                BoolLiteral(VelosiAstBoolLiteralExpr::new(l.val < r.val, self.loc))
            }
            (NumLiteral(l), Gt, NumLiteral(r)) => {
                BoolLiteral(VelosiAstBoolLiteralExpr::new(l.val > r.val, self.loc))
            }
            (NumLiteral(l), Ge, NumLiteral(r)) => {
                BoolLiteral(VelosiAstBoolLiteralExpr::new(l.val >= r.val, self.loc))
            }
            (NumLiteral(l), Le, NumLiteral(r)) => {
                BoolLiteral(VelosiAstBoolLiteralExpr::new(l.val <= r.val, self.loc))
            }
            // logical operators
            (BoolLiteral(l), Land, BoolLiteral(r)) => {
                BoolLiteral(VelosiAstBoolLiteralExpr::new(l.val && r.val, self.loc))
            }
            (BoolLiteral(l), Lor, BoolLiteral(r)) => {
                BoolLiteral(VelosiAstBoolLiteralExpr::new(l.val || r.val, self.loc))
            }
            (BoolLiteral(l), Implies, BoolLiteral(r)) => {
                BoolLiteral(VelosiAstBoolLiteralExpr::new(!l.val || r.val, self.loc))
            }
            _ => BinOp(self),
        }
    }

    pub fn flatten(
        self,
        st: &mut SymbolTable,
        mapping: &HashMap<Rc<String>, &VelosiAstExpr>,
    ) -> VelosiAstExpr {
        // here we could even be a bit smarter and try to further fold constants etc. using
        // further AST rewriting etc.

        let lhs = Rc::new(self.lhs.as_ref().clone().flatten(st, mapping));
        let rhs = Rc::new(self.rhs.as_ref().clone().flatten(st, mapping));

        VelosiAstBinOpExpr::new(lhs, self.op, rhs, self.loc).eval()
    }

    pub fn get_interface_references(&self, irefs: &mut HashSet<Rc<String>>) {
        self.lhs.get_interface_references(irefs);
        self.rhs.get_interface_references(irefs);
    }

    pub fn get_state_references(&self, srefs: &mut HashSet<Rc<String>>) {
        self.lhs.get_state_references(srefs);
        self.rhs.get_state_references(srefs);
    }

    pub fn has_state_references(&self) -> bool {
        self.lhs.has_state_references() || self.rhs.has_state_references()
    }

    pub fn has_interface_references(&self) -> bool {
        self.lhs.has_interface_references() || self.rhs.has_interface_references()
    }

    pub fn has_var_references(&self, vars: &HashSet<&str>) -> bool {
        self.lhs.has_var_references(vars) || self.rhs.has_var_references(vars)
    }

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        self.op.result_type()
    }

    pub fn get_var_references(&self) -> HashSet<&VelosiAstIdentLiteralExpr> {
        let mut vars = self.lhs.get_var_references();
        vars.extend(self.rhs.get_var_references());
        vars
    }
}

/// Implementation of [PartialEq] for [VelosiAstBinOpExpr]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstBinOpExpr {
    fn eq(&self, other: &Self) -> bool {
        self.op == other.op && self.lhs == other.lhs && self.rhs == other.rhs
    }
}

/// Implementation of [Hash] for [VelosiAstBinOpExpr]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstBinOpExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.op.hash(state);
        self.lhs.hash(state);
        self.rhs.hash(state);
    }
}

impl Display for VelosiAstBinOpExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        if self.lhs.needs_paren() {
            write!(format, "({})", self.lhs)?;
        } else {
            write!(format, "{}", self.lhs)?;
        }
        write!(format, " {} ", self.op)?;

        if self.rhs.needs_paren() {
            write!(format, "({})", self.rhs)
        } else {
            write!(format, "{}", self.rhs)
        }
    }
}

/// Implementation of [Debug] for [VelosiAstUnOp]
impl Debug for VelosiAstBinOpExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
