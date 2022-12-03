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

use std::collections::HashSet;
///! Ast Module of the Velosiraptor Compiler
// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used crate functionality
use crate::ast::{VelosiAstIdentifier, VelosiAstNode, VelosiAstParam};
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, SymbolTable};
use velosiparser::{
    VelosiParseTreeBinOp, VelosiParseTreeBinOpExpr, VelosiParseTreeBoolLiteral,
    VelosiParseTreeExpr, VelosiParseTreeFnCallExpr, VelosiParseTreeIdentifierLiteral,
    VelosiParseTreeIfElseExpr, VelosiParseTreeNumLiteral, VelosiParseTreeQuantifier,
    VelosiParseTreeQuantifierExpr, VelosiParseTreeRangeExpr, VelosiParseTreeSliceExpr,
    VelosiParseTreeUnOp, VelosiParseTreeUnOpExpr, VelosiTokenStream,
};

use super::VelosiAstTypeInfo;

///////////////////////////////////////////////////////////////////////////////////////////////////
// Binary Operation Expressions
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Binary operations for [VelosiAstExpr] <OP> [VelosiAstExpr]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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

/// Represents a binary operation `expr <op> expr`
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstBinOpExpr {
    pub lhs: Box<VelosiAstExpr>,
    pub op: VelosiAstBinOp,
    pub rhs: Box<VelosiAstExpr>,
    pub loc: VelosiTokenStream,
}

impl VelosiAstBinOpExpr {
    pub fn new(
        lhs: VelosiAstExpr,
        op: VelosiAstBinOp,
        rhs: VelosiAstExpr,
        loc: VelosiTokenStream,
    ) -> VelosiAstBinOpExpr {
        VelosiAstBinOpExpr {
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
            loc,
        }
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
            let hint = format!("No implementation for `{} {} {}`", lhs_type, op, rhs_type);

            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.clone())
                .build();
            issues.push(err);
        }

        // evaluate the expression, see if we can fold the constants
        let res = VelosiAstBinOpExpr::new(lhs, op, rhs, pt.loc).eval();

        if issues.is_ok() {
            AstResult::Ok(res)
        } else {
            AstResult::Issues(res, issues)
        }
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

    pub fn flatten(self, st: &mut SymbolTable) -> VelosiAstExpr {
        let lhs = self.lhs.flatten(st);
        let rhs = self.rhs.flatten(st);
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

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        self.op.result_type()
    }
}

impl Display for VelosiAstBinOpExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "({} {} {})", self.lhs, self.op, self.rhs)
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Unary Operation Expressions
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an unary operator
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstUnOpExpr {
    pub op: VelosiAstUnOp,
    pub expr: Box<VelosiAstExpr>,
    pub loc: VelosiTokenStream,
}

impl VelosiAstUnOpExpr {
    pub fn new(
        op: VelosiAstUnOp,
        expr: VelosiAstExpr,
        loc: VelosiTokenStream,
    ) -> VelosiAstUnOpExpr {
        VelosiAstUnOpExpr {
            op,
            expr: Box::new(expr),
            loc,
        }
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
            let hint = format!("No implementation for `{} {}`", op, expr_type);

            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.clone())
                .build();
            issues.push(err);
        }

        // evaluate the expression, see if we can fold the constants
        let res = VelosiAstUnOpExpr::new(op, expr, pt.loc).eval();

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
            (Not, NumLiteral(l)) => NumLiteral(VelosiAstNumLiteralExpr::new(!l.val, self.loc)),
            // boolean operators
            (LNot, BoolLiteral(l)) => BoolLiteral(VelosiAstBoolLiteralExpr::new(!l.val, self.loc)),
            _ => UnOp(self),
        }
    }

    pub fn flatten(self, st: &mut SymbolTable) -> VelosiAstExpr {
        match self.expr.flatten(st) {
            // the other expression is also an unary operation
            VelosiAstExpr::UnOp(e) => {
                // if the two unary opearations are the same, we can apply the double rule
                if self.op == e.op {
                    *e.expr
                } else {
                    VelosiAstUnOpExpr::new(self.op, VelosiAstExpr::UnOp(e), self.loc).eval()
                }
            }
            // the other expression is not unary, evaluate and return
            e => VelosiAstUnOpExpr::new(self.op, e, self.loc).eval(),
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

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        self.op.result_type()
    }
}

impl Display for VelosiAstUnOpExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}({})", self.op, self.expr)
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Quantifier Expression
///////////////////////////////////////////////////////////////////////////////////////////////////

/// representation of a quantifier
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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

/// Represents an unary operation
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstQuantifierExpr {
    pub quant: VelosiAstQuantifier,
    pub params: Vec<Rc<VelosiAstParam>>,
    pub expr: Box<VelosiAstExpr>,
    pub loc: VelosiTokenStream,
}

impl VelosiAstQuantifierExpr {
    pub fn new(
        quant: VelosiAstQuantifier,
        params: Vec<Rc<VelosiAstParam>>,
        expr: Box<VelosiAstExpr>,
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
                issues.push(e);
            } else {
                params.push(param);
            }
        }

        let expr = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.expr, st), issues);

        st.drop_context();

        let e = VelosiAstQuantifierExpr::new(quant, params, Box::new(expr), pt.loc);
        ast_result_return!(VelosiAstExpr::Quantifier(e), issues)
    }

    pub fn flatten(self, _st: &mut SymbolTable) -> VelosiAstExpr {
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

    pub fn has_interface_references(&self) -> bool {
        self.expr.has_interface_references()
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

///////////////////////////////////////////////////////////////////////////////////////////////////
// Literal Expressions
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an identifier literal expression
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstIdentLiteralExpr {
    pub ident: VelosiAstIdentifier,
    pub etype: VelosiAstTypeInfo,
    pub loc: VelosiTokenStream,
}

use core::str::Split;

impl VelosiAstIdentLiteralExpr {
    pub fn new(
        path: Vec<VelosiAstIdentifier>,
        etype: VelosiAstTypeInfo,
        loc: VelosiTokenStream,
    ) -> Self {
        let mut ident = path.first().unwrap().clone();
        for p in path.into_iter().skip(1) {
            ident.extend(p);
        }

        VelosiAstIdentLiteralExpr { ident, etype, loc }
    }

    pub fn with_name(name: String, ptype: VelosiAstTypeInfo) -> Self {
        VelosiAstIdentLiteralExpr::new(
            vec![VelosiAstIdentifier::with_name(name)],
            ptype,
            VelosiTokenStream::empty(),
        )
    }

    pub fn from_parse_tree(
        p: VelosiParseTreeIdentifierLiteral,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        // lookup the symbol in the symbol table

        let path = p
            .path
            .into_iter()
            .map(VelosiAstIdentifier::from)
            .collect::<Vec<VelosiAstIdentifier>>();

        let mut litexpr = VelosiAstIdentLiteralExpr::new(path, VelosiAstTypeInfo::Integer, p.loc);

        let tname = litexpr.path();
        let sym = st.lookup(tname);
        if sym.is_none() {
            let err = VelosiAstErrUndef::new(litexpr.ident().clone(), litexpr.loc.clone());
            return AstResult::Issues(VelosiAstExpr::IdentLiteral(litexpr), err.into());
        }

        let sym = sym.unwrap();

        match &sym.ast_node {
            VelosiAstNode::Const(c) => {
                debug_assert!(c.value.is_const_expr());
                // replace the identifier with the constant value
                AstResult::Ok(c.value.clone())
            }
            VelosiAstNode::Param(p) => {
                litexpr.etype = p.ptype.typeinfo.clone();
                AstResult::Ok(VelosiAstExpr::IdentLiteral(litexpr))
            }
            VelosiAstNode::StateField(_) | VelosiAstNode::StateFieldSlice(_) => {
                AstResult::Ok(VelosiAstExpr::IdentLiteral(litexpr))
            }
            VelosiAstNode::InterfaceField(_) | VelosiAstNode::InterfaceFieldSlice(_) => {
                AstResult::Ok(VelosiAstExpr::IdentLiteral(litexpr))
            }
            VelosiAstNode::Flag(_) => {
                litexpr.etype = VelosiAstTypeInfo::Flags;
                AstResult::Ok(VelosiAstExpr::IdentLiteral(litexpr))
            }
            _ => {
                // we have the wrong kind of symbol
                let err = VelosiAstErrUndef::with_other(
                    litexpr.path().clone(),
                    litexpr.loc.clone(),
                    sym.loc().clone(),
                );
                AstResult::Issues(VelosiAstExpr::IdentLiteral(litexpr), err.into())
            }
        }
    }

    pub fn flatten(self, st: &mut SymbolTable) -> VelosiAstExpr {
        let sym = st.lookup(self.path());
        if let Some(sym) = sym {
            match &sym.ast_node {
                VelosiAstNode::Const(c) => c.value.clone(),
                _ => VelosiAstExpr::IdentLiteral(self),
            }
        } else {
            VelosiAstExpr::IdentLiteral(self)
        }
    }

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        &self.etype
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

    pub fn path_split(&'_ self) -> Split<&'_ str> {
        self.ident.path_split()
    }

    /// obtains a copy of the fully qualified path
    pub fn path_to_string(&self) -> String {
        self.ident.path.as_str().to_string()
    }

    pub fn get_interface_references(&self, irefs: &mut HashSet<Rc<String>>) {
        if self.has_interface_references() {
            irefs.insert(self.path().clone());
        }
    }

    pub fn get_state_references(&self, srefs: &mut HashSet<Rc<String>>) {
        if self.has_state_references() {
            srefs.insert(self.path().clone());
        }
    }

    pub fn has_state_references(&self) -> bool {
        self.path().starts_with("state")
    }

    pub fn has_interface_references(&self) -> bool {
        self.path().starts_with("interface")
    }
}

/// Implementation of [Display] for [VelosiAstIdentLiteralExpr]
impl Display for VelosiAstIdentLiteralExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}", self.ident())
    }
}

/// Represents an numeric literal expression
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstNumLiteralExpr {
    pub val: u64,
    pub loc: VelosiTokenStream,
}

impl VelosiAstNumLiteralExpr {
    pub fn new(val: u64, loc: VelosiTokenStream) -> Self {
        VelosiAstNumLiteralExpr { val, loc }
    }

    pub fn from_parse_tree(
        p: VelosiParseTreeNumLiteral,
        _st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        // we can just convert the literal, as all values should be fine
        let e = VelosiAstNumLiteralExpr::new(p.value, p.loc);
        AstResult::Ok(VelosiAstExpr::NumLiteral(e))
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

    pub fn has_interface_references(&self) -> bool {
        false
    }
}

/// Implementation of [Display] for [VelosiAstNumLiteralExpr]
impl Display for VelosiAstNumLiteralExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}", self.val)
    }
}

impl From<u64> for VelosiAstNumLiteralExpr {
    fn from(val: u64) -> Self {
        Self::new(val, VelosiTokenStream::default())
    }
}

/// Represents an boolean literal expression
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstBoolLiteralExpr {
    pub val: bool,
    pub loc: VelosiTokenStream,
}

impl VelosiAstBoolLiteralExpr {
    pub fn new(val: bool, loc: VelosiTokenStream) -> Self {
        VelosiAstBoolLiteralExpr { val, loc }
    }

    pub fn from_parse_tree(
        p: VelosiParseTreeBoolLiteral,
        _st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        // we can just convert the literal, as all values should be fine
        let e = VelosiAstBoolLiteralExpr::new(p.value, p.loc);
        AstResult::Ok(VelosiAstExpr::BoolLiteral(e))
    }

    pub fn get_interface_references(&self, _irefs: &mut HashSet<Rc<String>>) {
        /* no-op */
    }

    pub fn get_state_references(&self, _srefs: &mut HashSet<Rc<String>>) {
        /* no op */
    }

    pub fn has_state_references(&self) -> bool {
        false
    }

    pub fn has_interface_references(&self) -> bool {
        false
    }
}

impl From<bool> for VelosiAstBoolLiteralExpr {
    fn from(val: bool) -> Self {
        Self::new(val, VelosiTokenStream::default())
    }
}

/// Implementation of [Display] for [VelosiAstBoolLiteralExpr]
impl Display for VelosiAstBoolLiteralExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}", self.val)
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Function Call Expression
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an boolean literal expression
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstFnCallExpr {
    pub ident: VelosiAstIdentifier,
    pub args: Vec<VelosiAstExpr>,
    pub etype: VelosiAstTypeInfo,
    pub loc: VelosiTokenStream,
}

impl VelosiAstFnCallExpr {
    pub fn new(
        ident: VelosiAstIdentifier,
        args: Vec<VelosiAstExpr>,
        etype: VelosiAstTypeInfo,
        loc: VelosiTokenStream,
    ) -> Self {
        VelosiAstFnCallExpr {
            ident,
            args,
            etype,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeFnCallExpr,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();
        let e = ast_result_unwrap!(Self::from_parse_tree_raw(pt, st), issues);
        ast_result_return!(VelosiAstExpr::FnCall(e), issues)
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
            args.push(arg);
        }

        // construct the default function call expression node
        let mut res = VelosiAstFnCallExpr::new(
            VelosiAstIdentifier::from(pt.name),
            args,
            VelosiAstTypeInfo::Integer,
            pt.loc,
        );

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

    pub fn flatten(self, st: &mut SymbolTable) -> VelosiAstExpr {
        VelosiAstExpr::FnCall(self.flatten_raw(st))
    }

    pub fn flatten_raw(self, st: &mut SymbolTable) -> Self {
        let mut res = self.clone();
        res.args = self.args.into_iter().map(|a| a.flatten(st)).collect();
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

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        &self.etype
    }
}

impl Display for VelosiAstFnCallExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}(", self.ident())?;
        for (i, p) in self.args.iter().enumerate() {
            if i != 0 {
                write!(format, ".")?;
            }
            write!(format, "{}", p)?;
        }
        write!(format, ")")
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// IF Else Expression
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an boolean literal expression
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstIfElseExpr {
    pub cond: Box<VelosiAstExpr>,
    pub then: Box<VelosiAstExpr>,
    pub other: Box<VelosiAstExpr>,
    pub etype: VelosiAstTypeInfo,
    pub loc: VelosiTokenStream,
}

impl VelosiAstIfElseExpr {
    pub fn new(
        cond: VelosiAstExpr,
        then: VelosiAstExpr,
        other: VelosiAstExpr,
        etype: VelosiAstTypeInfo,
        loc: VelosiTokenStream,
    ) -> Self {
        VelosiAstIfElseExpr {
            cond: Box::new(cond),
            then: Box::new(then),
            other: Box::new(other),
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
            let msg = format!("Expected boolean expression was {} expression.", cond_type);
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
            let hint = format!("Convert this expression into a {} exoression", then_type);

            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(cond.loc().clone())
                .build();
            issues.push(err);
        }

        let e = VelosiAstIfElseExpr::new(cond, then, other, then_type, pt.loc).flatten(st);
        if issues.is_ok() {
            AstResult::Ok(e)
        } else {
            AstResult::Issues(e, issues)
        }
    }

    pub fn flatten(self, st: &mut SymbolTable) -> VelosiAstExpr {
        let then = self.then.flatten(st);
        let other = self.other.flatten(st);
        let cond = self.cond.flatten(st);

        if let VelosiAstExpr::BoolLiteral(b) = &cond {
            if b.val {
                then
            } else {
                other
            }
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

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        &self.etype
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

///////////////////////////////////////////////////////////////////////////////////////////////////
// Range Expression
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an boolean literal expression
#[derive(PartialEq, Eq, Clone, Debug)]
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

    pub fn flatten(self, st: &mut SymbolTable) -> VelosiAstExpr {
        VelosiAstExpr::Range(self.flatten_raw(st))
    }

    pub fn flatten_raw(self, _st: &mut SymbolTable) -> Self {
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

    pub fn has_interface_references(&self) -> bool {
        false
    }
}

impl Display for VelosiAstRangeExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}..{}", self.start, self.end)
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Slice Expression
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an boolean literal expression
#[derive(PartialEq, Eq, Clone, Debug)]
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
        let name = ast_result_unwrap!(
            VelosiAstIdentLiteralExpr::from_parse_tree(pt.name, st),
            issues
        );

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

    pub fn flatten(self, st: &mut SymbolTable) -> VelosiAstExpr {
        if let VelosiAstExpr::Range(x) = self.range.flatten(st) {
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

    pub fn has_interface_references(&self) -> bool {
        self.ident.has_interface_references() || self.range.has_interface_references()
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

///////////////////////////////////////////////////////////////////////////////////////////////////
// Expressions
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an expression in the parse tree
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiAstExpr {
    IdentLiteral(VelosiAstIdentLiteralExpr),
    NumLiteral(VelosiAstNumLiteralExpr),
    BoolLiteral(VelosiAstBoolLiteralExpr),
    BinOp(VelosiAstBinOpExpr),
    UnOp(VelosiAstUnOpExpr),
    Quantifier(VelosiAstQuantifierExpr),
    FnCall(VelosiAstFnCallExpr),
    IfElse(VelosiAstIfElseExpr),
    Slice(VelosiAstSliceExpr),
    Range(VelosiAstRangeExpr),
}

impl VelosiAstExpr {
    pub fn from_parse_tree(
        p: VelosiParseTreeExpr,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        use VelosiParseTreeExpr::*;
        match p {
            Identifier(e) => VelosiAstIdentLiteralExpr::from_parse_tree(e, st),
            NumLiteral(e) => VelosiAstNumLiteralExpr::from_parse_tree(e, st),
            BoolLiteral(e) => VelosiAstBoolLiteralExpr::from_parse_tree(e, st),
            BinOp(e) => VelosiAstBinOpExpr::from_parse_tree(e, st),
            UnOp(e) => VelosiAstUnOpExpr::from_parse_tree(e, st),
            Quantifier(e) => VelosiAstQuantifierExpr::from_parse_tree(e, st),
            FnCall(e) => VelosiAstFnCallExpr::from_parse_tree(e, st),
            IfElse(e) => VelosiAstIfElseExpr::from_parse_tree(e, st),
            Slice(e) => VelosiAstSliceExpr::from_parse_tree(e, st),
            Range(e) => VelosiAstRangeExpr::from_parse_tree(e, st),
        }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(e) => &e.loc,
            NumLiteral(e) => &e.loc,
            BoolLiteral(e) => &e.loc,
            BinOp(e) => &e.loc,
            UnOp(e) => &e.loc,
            Quantifier(e) => &e.loc,
            FnCall(e) => &e.loc,
            IfElse(e) => &e.loc,
            Slice(e) => &e.loc,
            Range(e) => &e.loc,
        }
    }

    pub fn is_const_expr(&self) -> bool {
        use VelosiAstExpr::*;
        // when forming the expressions we do constant folding, so the
        // result should only be constant if its a literal
        matches!(self, NumLiteral(_) | BoolLiteral(_))
    }

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(e) => e.result_type(),
            NumLiteral(_) => &VelosiAstTypeInfo::Integer,
            BoolLiteral(_) => &VelosiAstTypeInfo::Bool,
            BinOp(e) => e.result_type(),
            UnOp(e) => e.result_type(),
            Quantifier(_) => &VelosiAstTypeInfo::Bool,
            FnCall(e) => e.result_type(),
            IfElse(e) => e.result_type(),
            Slice(e) => e.result_type(),
            Range(_) => &VelosiAstTypeInfo::Range,
        }
    }

    pub fn flatten(self, st: &mut SymbolTable) -> Self {
        use VelosiAstExpr::*;
        match self {
            BinOp(e) => e.flatten(st),
            UnOp(e) => e.flatten(st),
            Quantifier(e) => e.flatten(st),
            FnCall(e) => e.flatten(st),
            IfElse(e) => e.flatten(st),
            Slice(e) => e.flatten(st),
            Range(e) => e.flatten(st),
            IdentLiteral(e) => e.flatten(st),
            _ => self,
        }
    }

    pub fn has_interface_references(&self) -> bool {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(i) => i.has_interface_references(),
            NumLiteral(i) => i.has_interface_references(),
            BoolLiteral(i) => i.has_interface_references(),
            BinOp(i) => i.has_interface_references(),
            UnOp(i) => i.has_interface_references(),
            Quantifier(i) => i.has_interface_references(),
            FnCall(i) => i.has_interface_references(),
            IfElse(i) => i.has_interface_references(),
            Slice(i) => i.has_interface_references(),
            Range(i) => i.has_interface_references(),
        }
    }

    pub fn has_state_references(&self) -> bool {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(i) => i.has_state_references(),
            NumLiteral(i) => i.has_state_references(),
            BoolLiteral(i) => i.has_state_references(),
            BinOp(i) => i.has_state_references(),
            UnOp(i) => i.has_state_references(),
            Quantifier(i) => i.has_state_references(),
            FnCall(i) => i.has_state_references(),
            IfElse(i) => i.has_state_references(),
            Slice(i) => i.has_state_references(),
            Range(i) => i.has_state_references(),
        }
    }

    pub fn get_state_references(&self, srefs: &mut HashSet<Rc<String>>) {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(i) => i.get_state_references(srefs),
            NumLiteral(i) => i.get_state_references(srefs),
            BoolLiteral(i) => i.get_state_references(srefs),
            BinOp(i) => i.get_state_references(srefs),
            UnOp(i) => i.get_state_references(srefs),
            Quantifier(i) => i.get_state_references(srefs),
            FnCall(i) => i.get_state_references(srefs),
            IfElse(i) => i.get_state_references(srefs),
            Slice(i) => i.get_state_references(srefs),
            Range(i) => i.get_state_references(srefs),
        };
    }

    pub fn get_interface_references(&self, irefs: &mut HashSet<Rc<String>>) {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(i) => i.get_interface_references(irefs),
            NumLiteral(i) => i.get_interface_references(irefs),
            BoolLiteral(i) => i.get_interface_references(irefs),
            BinOp(i) => i.get_interface_references(irefs),
            UnOp(i) => i.get_interface_references(irefs),
            Quantifier(i) => i.get_interface_references(irefs),
            FnCall(i) => i.get_interface_references(irefs),
            IfElse(i) => i.get_interface_references(irefs),
            Slice(i) => i.get_interface_references(irefs),
            Range(i) => i.get_interface_references(irefs),
        };
    }

    // converts a boolean expression into the conjunctive normal form
    pub fn into_cnf(self, st: &mut SymbolTable) -> Self {
        use VelosiAstBinOp::*;
        use VelosiAstExpr::*;
        use VelosiAstUnOp::*;

        if let BinOp(outer) = &self {
            // distributive law

            // (p or (q and r)) == (p or q) and (p or r)
            if let BinOp(inner) = outer.rhs.as_ref() {
                if outer.op == Lor && inner.op == Land {
                    let lhs = VelosiAstBinOpExpr::new(
                        *outer.lhs.clone(),
                        Lor,
                        *inner.lhs.clone(),
                        outer.loc.clone(),
                    )
                    .flatten(st);
                    let rhs = VelosiAstBinOpExpr::new(
                        *outer.lhs.clone(),
                        Lor,
                        *inner.rhs.clone(),
                        outer.loc.clone(),
                    )
                    .flatten(st);
                    let res =
                        VelosiAstBinOpExpr::new(lhs, Land, rhs, outer.loc.clone()).flatten(st);
                    // println!("into_cnf | rewrite: applying distributive law");
                    // println!("  {} -> {}", self, res);
                    return res;
                }
            }

            // ((q and r) or p) == (p or q) and (p or r)
            if let BinOp(inner) = outer.lhs.as_ref() {
                if outer.op == Lor && inner.op == Land {
                    // println!("into_cnf | rewrite: applying distributive law");
                    let lhs = VelosiAstBinOpExpr::new(
                        *outer.rhs.clone(),
                        Lor,
                        *inner.lhs.clone(),
                        outer.loc.clone(),
                    )
                    .flatten(st);
                    let rhs = VelosiAstBinOpExpr::new(
                        *outer.rhs.clone(),
                        Lor,
                        *inner.rhs.clone(),
                        outer.loc.clone(),
                    )
                    .flatten(st);
                    let res =
                        VelosiAstBinOpExpr::new(lhs, Land, rhs, outer.loc.clone()).flatten(st);
                    // println!("into_cnf | rewrite: applying distributive law");
                    // println!("  {} -> {}", self, res);
                    return res;
                }
            }
        } else if let UnOp(ue) = &self {
            if let BinOp(be) = ue.expr.as_ref() {
                // demorgan's law
                // !(p or q) == !p and !q
                if ue.op == LNot && be.op == Lor {
                    let lhs =
                        VelosiAstUnOpExpr::new(LNot, *be.lhs.clone(), be.loc.clone()).flatten(st);
                    let rhs =
                        VelosiAstUnOpExpr::new(LNot, *be.rhs.clone(), be.loc.clone()).flatten(st);
                    let res = VelosiAstBinOpExpr::new(lhs, Land, rhs, ue.loc.clone()).flatten(st);
                    // println!("into_cnf | rewrite: applying demorgan's law");
                    // println!("  {} -> {}", self, res);
                    return res;
                }
            }
        }
        self
    }

    /// splits a boolean expression into is conjuncts
    pub fn split_cnf(self) -> Vec<Self> {
        use VelosiAstExpr::*;
        match self {
            BinOp(e) => {
                if e.op == VelosiAstBinOp::Land {
                    let mut v = e.lhs.split_cnf();
                    v.extend(e.rhs.split_cnf());
                    v
                } else {
                    vec![BinOp(e)]
                }
            }
            e => vec![e],
        }
    }

    /// returns true if the expression is an lvalue
    pub fn is_lvalue(&self) -> bool {
        use VelosiAstExpr::*;
        matches!(self, IdentLiteral(_) | Slice(_))
    }
}

/// Implementation of [Display] for [VelosiAstExpr]
impl Display for VelosiAstExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(i) => Display::fmt(&i, format),
            NumLiteral(i) => Display::fmt(&i, format),
            BoolLiteral(i) => Display::fmt(&i, format),
            BinOp(i) => Display::fmt(&i, format),
            UnOp(i) => Display::fmt(&i, format),
            Quantifier(i) => Display::fmt(&i, format),
            FnCall(i) => Display::fmt(&i, format),
            IfElse(i) => Display::fmt(&i, format),
            Slice(i) => Display::fmt(&i, format),
            Range(i) => Display::fmt(&i, format),
        }
    }
}

// #[cfg(test)]
// use crate::lexer::Lexer;
// #[cfg(test)]
// use crate::parser::expression::{arith_expr, bool_expr};
// #[cfg(test)]
// use crate::sourcepos::SourcePos;

// #[cfg(test)]
// macro_rules! parse_equal (
//     ($parser:expr, $lhs:expr, $rhs:expr) => (
//         let sp = SourcePos::new("stdio", $lhs);
//         let tokens = Lexer::lex_source_pos(sp).unwrap();
//         let ts = TokenStream::from_vec(tokens);
//         let (_, ex) = $parser(ts.clone()).unwrap();
//         assert_eq!(
//             format!("{}", ex.fold_constants(&SymbolTable::new(), &HashMap::new())),
//             String::from($rhs)
//         );
//     )
// );

// #[test]
// fn const_folding_test() {
//     parse_equal!(arith_expr, "1+3", "4");
//     parse_equal!(arith_expr, "1+3*4", "13");
//     parse_equal!(bool_expr, "true && false", "false");
//     parse_equal!(bool_expr, "true || false", "true");
//     //assert_eq!(ex.map(|(i, x)| (i, format!("{}", x))), String::from("4"));
// }
