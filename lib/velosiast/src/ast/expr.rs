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

///! Ast Module of the Velosiraptor Compiler
// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used crate functionality
use crate::ast::VelosiAstNode;
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::{ast_result_unwrap, AstResult, SymbolTable};
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
            Eq | Ne => !rhs_type.compatible(lhs_type),
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

    pub fn result_type(&self, _st: &SymbolTable) -> &VelosiAstTypeInfo {
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
    lhs: Box<VelosiAstExpr>,
    op: VelosiAstBinOp,
    rhs: Box<VelosiAstExpr>,
    loc: VelosiTokenStream,
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
        st: &SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convet the lhs/rhs and operator
        let op = VelosiAstBinOp::from(pt.op);
        let lhs = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.lhs, st), issues);
        let rhs = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.rhs, st), issues);

        // obtain the result types
        let lhs_type = lhs.result_type(st);
        let rhs_type = rhs.result_type(st);

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

    pub fn flatten(self, st: &SymbolTable) -> VelosiAstExpr {
        let lhs = self.lhs.flatten(st);
        let rhs = self.rhs.flatten(st);
        VelosiAstBinOpExpr::new(lhs, self.op, rhs, self.loc).eval()
    }

    pub fn result_type(&self, st: &SymbolTable) -> &VelosiAstTypeInfo {
        self.op.result_type(st)
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

    pub fn result_type(&self, _st: &SymbolTable) -> &VelosiAstTypeInfo {
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
    op: VelosiAstUnOp,
    expr: Box<VelosiAstExpr>,
    loc: VelosiTokenStream,
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
        st: &SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convet the lhs/rhs and operator
        let op = VelosiAstUnOp::from(pt.op);
        let expr = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.expr, st), issues);

        // obtain the result types
        let expr_type = expr.result_type(st);

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

    pub fn flatten(self, st: &SymbolTable) -> VelosiAstExpr {
        let val = self.expr.flatten(st);
        VelosiAstUnOpExpr::new(self.op, val, self.loc).eval()
    }

    pub fn result_type(&self, st: &SymbolTable) -> &VelosiAstTypeInfo {
        self.op.result_type(st)
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
    quant: VelosiAstQuantifier,
    //params: // Vec<VelosiAstParam>,
    expr: Box<VelosiAstExpr>,
    loc: VelosiTokenStream,
}

impl VelosiAstQuantifierExpr {
    // pub fn new(
    //     quant: VelosiAstQuantifier,
    //     params: Vec<VelosiAstParam>,
    //     expr: Box<VelosiAstExpr>,
    //     loc: VelosiTokenStream,
    // ) -> VelosiAstQuantifierExpr {
    //     VelosiAstQuantifierExpr {
    //         quant,
    //         params,
    //         expr,
    //         loc,
    //     }
    // }

    pub fn from_parse_tree(
        _p: VelosiParseTreeQuantifierExpr,
        _st: &SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        panic!("nyi");

        // let quant = VelosiAstQuantifier::from(p.quant);
        // let expr = VelosiAstExpr::from_parse_tree(p.expr, _st).unwrap();

        // let e = VelosiAstQuantifierExpr::new(quant, params, expr, p.loc);
        // Ok(VelosiAstExpr::Quantifier(e))
    }

    pub fn flatten(self, _st: &SymbolTable) -> VelosiAstExpr {
        panic!("nyi");
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
    path: Vec<String>,
    etype: VelosiAstTypeInfo,
    loc: VelosiTokenStream,
}

impl VelosiAstIdentLiteralExpr {
    pub fn new(path: Vec<String>, etype: VelosiAstTypeInfo, loc: VelosiTokenStream) -> Self {
        VelosiAstIdentLiteralExpr { path, etype, loc }
    }

    pub fn from_parse_tree(
        p: VelosiParseTreeIdentifierLiteral,
        st: &SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        // lookup the symbol in the symbol table

        let litexpr = VelosiAstIdentLiteralExpr::new(p.path, VelosiAstTypeInfo::Integer, p.loc);
        let tname = litexpr.path.join(".");

        let sym = st.lookup(tname.as_str());
        if sym.is_none() {
            let err = VelosiAstErrUndef::new(Rc::new(tname), litexpr.loc.clone());
            return AstResult::Issues(VelosiAstExpr::IdentLiteral(litexpr), err.into());
        }

        let sym = sym.unwrap();
        match &sym.ast_node {
            VelosiAstNode::Const(c) => {
                debug_assert!(c.value.is_const_expr());
                // replace the identifier with the constant value
                AstResult::Ok(c.value.clone())
            }
            VelosiAstNode::Param(_p) => {
                // // litexpr.etype = p.ptype;
                // AstResult::Ok(VelosiAstExpr::IdentLiteral(litexpr));
                panic!("nyi")
            }
            _ => {
                // we have the wrong kind of symbol
                let err = VelosiAstErrUndef::with_other(
                    Rc::new(tname),
                    litexpr.loc.clone(),
                    sym.loc().clone(),
                );
                AstResult::Issues(VelosiAstExpr::IdentLiteral(litexpr), err.into())
            }
        }
    }

    pub fn result_type(&self, _st: &SymbolTable) -> &VelosiAstTypeInfo {
        &self.etype
    }
}

/// Implementation of [Display] for [VelosiAstIdentLiteralExpr]
impl Display for VelosiAstIdentLiteralExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}", self.path.join("."))
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
        _st: &SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        // we can just convert the literal, as all values should be fine
        let e = VelosiAstNumLiteralExpr::new(p.value, p.loc);
        AstResult::Ok(VelosiAstExpr::NumLiteral(e))
    }
}

/// Implementation of [Display] for [VelosiAstNumLiteralExpr]
impl Display for VelosiAstNumLiteralExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}", self.val)
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
        _st: &SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        // we can just convert the literal, as all values should be fine
        let e = VelosiAstBoolLiteralExpr::new(p.value, p.loc);
        AstResult::Ok(VelosiAstExpr::BoolLiteral(e))
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
    pub path: String,
    pub args: Vec<VelosiAstExpr>,
    pub etype: VelosiAstTypeInfo,
    pub loc: VelosiTokenStream,
}

impl VelosiAstFnCallExpr {
    pub fn new(
        path: String,
        args: Vec<VelosiAstExpr>,
        etype: VelosiAstTypeInfo,
        loc: VelosiTokenStream,
    ) -> Self {
        VelosiAstFnCallExpr {
            path,
            args,
            etype,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeFnCallExpr,
        st: &SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // process the function call arguments
        let mut args = Vec::with_capacity(pt.args.len());
        for a in pt.args.into_iter() {
            let arg = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(a, st), issues);
            args.push(arg);
        }

        // construct the default function call expression node
        let res = VelosiAstFnCallExpr::new(
            pt.path.to_string(),
            args,
            VelosiAstTypeInfo::Integer,
            pt.loc,
        );

        //     error[E0061]: this function takes 5 arguments but 4 arguments were supplied
        //     --> lib/velosiast/src/ast/expr.rs:937:21
        //      |
        //  937 |             let e = VelosiAstIfElseExpr::new(cond, then, other, self.loc);
        //      |                     ^^^^^^^^^^^^^^^^^^^^^^^^                    -------- an argument of type `VelosiAstTypeInfo` is missing
        //      |

        //     error[E0308]: mismatched types
        //     --> lib/velosiast/src/ast/expr.rs:822:31
        //      |
        //  822 |             AstResult::Issues(res, issues)
        //      |             ----------------- ^^^ expected enum `VelosiAstExpr`, found struct `VelosiAstFnCallExpr`
        //      |             |
        //      |             arguments to this enum variant are incorrect

        let fn_name = pt.path.to_string();

        let fn_sym = st.lookup(fn_name.as_str());
        if fn_sym.is_none() {
            // there was no symbol
            let err = VelosiAstErrUndef::new(Rc::new(fn_name), res.loc.clone());
            return AstResult::Issues(VelosiAstExpr::FnCall(res), err.into());
        }

        let fn_sym = fn_sym.unwrap();
        if let VelosiAstNode::Method(_m) = &fn_sym.ast_node {
            panic!("not implemented");
        } else {
            // we have the wrong kind of symbol
            let err = VelosiAstErrUndef::with_other(
                Rc::new(fn_name),
                res.loc.clone(),
                fn_sym.loc().clone(),
            );
            return AstResult::Issues(VelosiAstExpr::FnCall(res), err.into());
        }

        if issues.is_ok() {
            AstResult::Ok(VelosiAstExpr::FnCall(res))
        } else {
            AstResult::Issues(VelosiAstExpr::FnCall(res), issues)
        }
    }

    pub fn flatten(self, st: &SymbolTable) -> VelosiAstExpr {
        let args = self.args.into_iter().map(|a| a.flatten(st)).collect();
        VelosiAstExpr::FnCall(Self::new(self.path, args, self.etype, self.loc))
    }

    pub fn result_type(&self, _st: &SymbolTable) -> &VelosiAstTypeInfo {
        &self.etype
    }
}

impl Display for VelosiAstFnCallExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}(", self.path)?;
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
        st: &SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        let cond = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.cond, st), issues);
        let then = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.then, st), issues);
        let other = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*pt.other, st), issues);

        let cond_type = cond.result_type(st);
        if *cond_type != VelosiAstTypeInfo::Bool {
            let msg = format!("Expected boolean expression was {} expression.", cond_type);
            let hint = "Convert this expression into a boolean expression";

            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint.to_string())
                .add_location(cond.loc().clone())
                .build();
            issues.push(err);
        }

        let then_type = then.result_type(st).clone();
        let other_type = other.result_type(st);

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

    pub fn flatten(self, st: &SymbolTable) -> VelosiAstExpr {
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
            let restype = then.result_type(st).clone();
            let e = VelosiAstIfElseExpr::new(cond, then, other, restype, self.loc);
            VelosiAstExpr::IfElse(e)
        }
    }

    pub fn result_type(&self, _st: &SymbolTable) -> &VelosiAstTypeInfo {
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
    pub fn from_parse_tree(
        _p: VelosiParseTreeRangeExpr,
        _st: &SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        panic!("nyi!");
    }

    pub fn flatten(self, _st: &SymbolTable) -> VelosiAstExpr {
        VelosiAstExpr::Range(self)
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
    pub name: VelosiAstIdentLiteralExpr,
    pub range: VelosiAstRangeExpr,
    pub loc: VelosiTokenStream,
}

impl VelosiAstSliceExpr {
    pub fn new(
        name: VelosiAstIdentLiteralExpr,
        range: VelosiAstRangeExpr,
        loc: VelosiTokenStream,
    ) -> Self {
        VelosiAstSliceExpr { name, range, loc }
    }
    pub fn from_parse_tree(
        _p: VelosiParseTreeSliceExpr,
        _st: &SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        panic!("nyi!");
    }

    pub fn flatten(self, _st: &SymbolTable) -> VelosiAstExpr {
        panic!("nyi!");
        // VelosiAstExpr::Slice(Self::new(self.name, self.range.flatten(st), self.loc))
    }

    pub fn result_type(&self, _st: &SymbolTable) -> &VelosiAstTypeInfo {
        panic!("nyi!");
    }
}

impl Display for VelosiAstSliceExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(
            format,
            "{}[{}..{}]",
            self.name, self.range.start, self.range.end
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
        st: &SymbolTable,
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

    pub fn result_type(&self, st: &SymbolTable) -> &VelosiAstTypeInfo {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(e) => e.result_type(st),
            NumLiteral(_) => &VelosiAstTypeInfo::Integer,
            BoolLiteral(_) => &VelosiAstTypeInfo::Bool,
            BinOp(e) => e.result_type(st),
            UnOp(e) => e.result_type(st),
            Quantifier(_) => &VelosiAstTypeInfo::Bool,
            FnCall(e) => e.result_type(st),
            IfElse(e) => e.result_type(st),
            Slice(e) => e.result_type(st),
            Range(_) => &VelosiAstTypeInfo::Range,
        }
    }

    pub fn flatten(self, st: &SymbolTable) -> Self {
        use VelosiAstExpr::*;
        match self {
            BinOp(e) => e.flatten(st),
            UnOp(e) => e.flatten(st),
            Quantifier(e) => e.flatten(st),
            FnCall(e) => e.flatten(st),
            IfElse(e) => e.flatten(st),
            Slice(e) => e.flatten(st),
            Range(e) => e.flatten(st),
            _ => self,
        }
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

// /// Represents an Expression
// ///
// /// The expressions form a trie that is the being evaluated bottom up.
// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum Expr {
//     /// Represents an identifier. That may be qualified or not.  `a.b`
//     Identifier { path: Vec<String>, pos: TokenStream },
//     /// Represents a constant, unsigned number  `5`
//     Number { value: u64, pos: TokenStream },
//     /// Represents a constant boolean value  `True | False`
//     Boolean { value: bool, pos: TokenStream },
//     /// Represents a binary operation  `a + 1`
//     BinaryOperation {
//         op: BinOp,
//         lhs: Box<Expr>,
//         rhs: Box<Expr>,
//         pos: TokenStream,
//     },
//     /// Represents an unary operation `!a`
//     UnaryOperation {
//         op: UnOp,
//         val: Box<Expr>,
//         pos: TokenStream,
//     },
//     /// Represents a function call  `a.b(x,y)`
//     FnCall {
//         path: Vec<String>,        let lhs = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*p.lhs, st), issues);
//let rhs = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(*p.rhs, st), issues);
//         args: Vec<Expr>,
//         pos: TokenStream,
//     },
//     /// Represents a slice  `a[1..x]`
//     Slice {
//         path: Vec<String>,
//         slice: Box<Expr>,
//         pos: TokenStream,
//     },
//     /// Represents an element aaccess `a[0]`
//     Element {
//         path: Vec<String>,
//         idx: Box<Expr>,
//         pos: TokenStream,
//     },
//     /// Represents a range  `start..end`
//     Range {
//         start: Box<Expr>,
//         end: Box<Expr>,
//         pos: TokenStream,
//     },
//     /// Represents a quantifier `forall x | x > 0`
//     Quantifier {
//         kind: Quantifier,
//         vars: Vec<Param>,
//         expr: Box<Expr>,
//         pos: TokenStream,
//     },
// }

// /// Implementation of [Expr]
// impl<'a> Expr {
//     /// applies constant folding
//     pub fn fold_constants(&self, st: &SymbolTable, vars: &HashMap<String, u64>) -> Self {
//         use Expr::*;
//         match self {
//             Number { value, pos } => Number {
//                 value: *value,
//                 pos: pos.clone(),
//             },
//             Boolean { value, pos } => Boolean {
//                 value: *value,
//                 pos: pos.clone(),
//             },
//             Identifier { path, pos } => {
//                 let v = path.join(".");
//                 if let Some(val) = vars.get(&v) {
//                     Number {
//                         value: *val,
//                         pos: pos.clone(),
//                     }
//                 } else if let Some(val) = st.lookup(&v) {
//                     if let AstNode::Const(c) = val.ast_node {
//                         c.to_expr().fold_constants(st, vars)
//                     } else {
//                         panic!("{} is not a constant", v)
//                     }
//                 } else {
//                     panic!("{} is not defined", v)
//                 }
//             }
//             BinaryOperation { op, lhs, rhs, pos } => {
//                 let lhs = lhs.fold_constants(st, vars);
//                 let rhs = rhs.fold_constants(st, vars);
//                 op.eval(lhs, rhs, pos.clone())
//             }
//             UnaryOperation { op, val, pos } => {
//                 let val = val.fold_constants(st, vars);
//                 op.eval(val, pos.clone())
//             }
//             FnCall { path, args, pos } => {
//                 let args = args.iter().map(|e| e.fold_constants(st, vars)).collect();
//                 FnCall {
//                     path: path.clone(),
//                     args,
//                     pos: pos.clone(),
//                 }
//             }
//             Slice { path, slice, pos } => {
//                 let slice = slice.fold_constants(st, vars);
//                 Slice {
//                     path: path.clone(),
//                     slice: Box::new(slice),
//                     pos: pos.clone(),
//                 }
//             }
//             Element { path, idx, pos } => {
//                 let idx = idx.fold_constants(st, vars);
//                 Element {
//                     path: path.clone(),
//                     idx: Box::new(idx),
//                     pos: pos.clone(),
//                 }
//             }
//             Range { start, end, pos } => {
//                 let start = start.fold_constants(st, vars);
//                 let end = end.fold_constants(st, vars);
//                 Range {
//                     start: Box::new(start),
//                     end: Box::new(end),
//                     pos: pos.clone(),
//                 }
//             }
//             Quantifier {
//                 kind,
//                 vars: lvars,
//                 expr,
//                 pos,
//             } => {
//                 let expr = expr.fold_constants(st, vars);
//                 Quantifier {
//                     kind: *kind,
//                     vars: lvars.clone(),
//                     expr: Box::new(expr),
//                     pos: pos.clone(),
//                 }
//             }
//         }
//     }

//     /// returns true if the expression is a constant expression
//     ///
//     /// it consults the symbol table to figure out whether the symbol / variable is constant
//     pub fn is_const_expr(&self, st: &SymbolTable) -> bool {
//         use Expr::*;
//         match self {
//             // numbers and booleans are constant
//             Number { .. } => true,
//             Boolean { .. } => true,
//             // unary and binary operations are constant, if and only if each operand is constnat
//             BinaryOperation { lhs, rhs, .. } => lhs.is_const_expr(st) && rhs.is_const_expr(st),
//             UnaryOperation { val, .. } => val.is_const_expr(st),
//             // an identifyer is constnat, if its in the symbol table as a constant
//             Identifier { path, .. } => {
//                 // TODO: deal with context.symbol
//                 let name = path.join(".");
//                 match st.lookup(&name) {
//                     Some(s) => s.is_const(),
//                     None => false,
//                 }
//             }
//             // everything else is not constant
//             _ => false,
//         }
//     }

//     /// returns true if the expression is an lvalue
//     pub fn is_lvalue(&self) -> bool {
//         use Expr::*;
//         matches!(self, Identifier { .. } | Slice { .. } | Element { .. })
//     }

//     /// matches a symbol with a given type
//     pub fn match_symbol(path: &[String], pos: &TokenStream, ty: Type, st: &SymbolTable) -> Issues {
//         let name = path.join(".");
//         match st.lookup(&name) {
//             Some(s) => {
//                 if !ty.compatible(s.typeinfo) {
//                     // warning
//                     let msg = format!(
//                         "expected expression of type `{}`, {} symbol `{}` has type `{}`",
//                         ty.to_type_string(),
//                         s.kind,
//                         name,
//                         s.typeinfo.to_type_string()
//                     );
//                     let hint = String::from("define symbol with matching type");
//                     VrsError::new_err(pos, msg, Some(hint)).print();
//                     Issues::err()
//                 } else {
//                     Issues::ok()
//                 }
//             }
//             None => {
//                 // warning
//                 let msg = format!(
//                     "expected expression of type `{}`, symbol `{}` was not found",
//                     ty.to_type_string(),
//                     name
//                 );
//                 let hint = format!("define symbol with type `{}`", ty.to_type_string());
//                 VrsError::new_err(pos, msg, Some(hint)).print();
//                 Issues::err()
//             }
//         }
//     }

//     /// matches the type of the expressin with the supplied type
//     pub fn match_type(&self, ty: Type, st: &SymbolTable) -> Issues {
//         use Expr::*;
//         match self {
//             // numbers and booleans are constant
//             Number { pos, .. } => {
//                 if !ty.is_numeric() {
//                     // warning
//                     let msg = format!(
//                         "expected expression of type `{}`, but was of numeric type.`",
//                         ty.to_type_string()
//                     );
//                     let hint = format!("convert to `{}` type.", ty.to_type_string());
//                     VrsError::new_err(pos, msg, Some(hint)).print();
//                     Issues::err()
//                 } else {
//                     Issues::ok()
//                 }
//             }
//             Boolean { pos, .. } => {
//                 if !ty.is_boolean() {
//                     // warning
//                     let msg = format!(
//                         "expected expression of type `{}`, but was of boolean type.`",
//                         ty.to_type_string()
//                     );
//                     let hint = format!("convert to `{}` type.", ty.to_type_string());
//                     VrsError::new_err(pos, msg, Some(hint)).print();
//                     Issues::err()
//                 } else {
//                     Issues::ok()
//                 }
//             }
//             // unary and binary operations are constant, if and only if each operand is constnat
//             BinaryOperation { op, pos, .. } => {
//                 if op.result_boolean() && ty.is_boolean() || op.result_numeric() && ty.is_numeric()
//                 {
//                     Issues::ok()
//                 } else {
//                     // warning
//                     let msg = format!("expected expression of type `{}`", ty.to_type_string(),);
//                     let hint = format!(
//                         "change expression to produce `{}` or change type",
//                         ty.to_type_string()
//                     );
//                     VrsError::new_err(pos, msg, Some(hint)).print();
//                     Issues::err()
//                 }
//             }
//             UnaryOperation { val, .. } => val.match_type(ty, st),
//             // an identifyer is constnat, if its in the symbol table as a constant
//             Identifier { path, pos } => Self::match_symbol(path, pos, ty, st),
//             FnCall { path, pos, .. } => Self::match_symbol(path, pos, ty, st),
//             Element { path, pos, .. } => Self::match_symbol(path, pos, ty, st),
//             Quantifier { pos, .. } => {
//                 if ty.is_boolean() {
//                     Issues::ok()
//                 } else {
//                     let msg = format!(
//                         "expected expression of type `{}`, but quantifier is boolean",
//                         ty.to_type_string(),
//                     );
//                     VrsError::new_err(pos, msg, None).print();
//                     Issues::err()
//                 }
//             }
//             // everything else is currently not supported
//             x => {
//                 // warning
//                 let msg = format!(
//                     "expected expression of type `{}`, but found unsupported exprssion {}",
//                     ty.to_type_string(),
//                     x
//                 );
//                 let hint = format!(
//                     "change expression to produce `{}` or change type",
//                     ty.to_type_string()
//                 );
//                 VrsError::new_err(x.loc(), msg, Some(hint)).print();
//                 Issues::err()
//             }
//         }
//     }

//     /// checks if a given symbol exists with the path
//     fn symbol_exists(
//         pos: &TokenStream,
//         path: &[String],
//         st: &SymbolTable,
//         kind: &[SymbolKind],
//     ) -> Issues {
//         let ident = path.join(".");
//         match st.lookup(&ident) {
//             Some(s) => {
//                 if !kind.contains(&s.kind) {
//                     // warning
//                     let msg = format!(
//                         "symbol `{}` exists but has a wrong kind. Expected `{:?}`, was `{:?}`",
//                         ident, kind, s.kind
//                     );
//                     let hint = format!(
//                         "define this symbol as {:?}, or converts its use to {:?}",
//                         kind, s.kind
//                     );
//                     VrsError::new_err(pos, msg, Some(hint)).print();
//                     Issues::err()
//                 } else {
//                     Issues::ok()
//                 }
//             }
//             None => {
//                 let msg = format!("symbol `{}` does not exist within this context", ident);
//                 VrsError::new_err(pos, msg, None).print();
//                 Issues::err()
//             }
//         }
//     }

//     /// checks that all symbols are defined in the exprssions
//     pub fn check_symbols(&'a self, st: &mut SymbolTable<'a>) -> Issues {
//         let varkind = &[
//             SymbolKind::Const,
//             SymbolKind::Parameter,
//             SymbolKind::Variable,
//             SymbolKind::State,
//         ];
//         let fnkind = &[SymbolKind::Function];
//         use Expr::*;
//         match self {
//             Identifier { path, pos } => Expr::symbol_exists(pos, path, st, varkind),
//             Number { .. } => Issues::ok(),
//             Boolean { .. } => Issues::ok(),
//             BinaryOperation { lhs, rhs, .. } => lhs.check_symbols(st) + rhs.check_symbols(st),
//             UnaryOperation { val, .. } => val.check_symbols(st),
//             FnCall { path, args, pos } => {
//                 let s = Expr::symbol_exists(pos, path, st, fnkind);
//                 args.iter().fold(s, |acc, e| e.check_symbols(st) + acc)
//             }
//             Slice { path, slice, pos } => {
//                 // currently we can't do foo()[]
//                 let s = Expr::symbol_exists(pos, path, st, varkind);
//                 s + slice.check_symbols(st)
//             }
//             Element { path, idx, pos } => {
//                 let s = Expr::symbol_exists(pos, path, st, varkind);
//                 s + idx.check_symbols(st)
//             }
//             Range { start, end, .. } => start.check_symbols(st) + end.check_symbols(st),
//             Quantifier { vars, expr, .. } => {
//                 let mut issues = Issues::ok();
//                 // create st context
//                 st.create_context(String::from("quantifier"));
//                 issues.inc_err(utils::check_double_entries(vars));
//                 for v in vars {
//                     if let Some(s) = st.lookup(&v.name) {
//                         let msg = format!(
//                             "identifier `{}` shadows a previously defined symbol",
//                             s.name
//                         );
//                         let hint = String::from("consider giving the variable another name");
//                         VrsError::new_warn(v.loc(), msg, Some(hint)).print();
//                         issues.inc_warn(1);
//                     }
//                     issues = issues + utils::check_snake_case(&v.name, v.loc());
//                     st.insert(v.to_symbol());
//                 }

//                 issues = issues + expr.check_symbols(st) + expr.match_type(Type::Boolean, st);

//                 // pop systable context
//                 st.drop_context();

//                 issues
//             }
//         }
//     }

//     /// checks if the types of the expression match
//     pub fn check_types(&self, _st: &mut SymbolTable) -> Issues {
//         Issues::ok()
//     }

//     fn path_to_hashset(path: &[String]) -> HashSet<String> {
//         let mut hs = HashSet::new();
//         hs.insert(path.join("."));
//         hs
//     }

//     /// obtains the state references of this expression
//     fn get_state_interface_references(&self, prefix: &str) -> HashSet<String> {
//         use Expr::*;
//         match self {
//             Identifier { path, .. } => {
//                 if path[0] == prefix {
//                     Expr::path_to_hashset(path)
//                 } else {
//                     HashSet::new()
//                 }
//             }
//             Number { .. } => HashSet::new(),
//             Boolean { .. } => HashSet::new(),
//             BinaryOperation { lhs, rhs, .. } => {
//                 let mut v = lhs.get_state_interface_references(prefix);
//                 v.extend(rhs.get_state_interface_references(prefix));
//                 v
//             }
//             UnaryOperation { val, .. } => val.get_state_interface_references(prefix),
//             FnCall { path, args, .. } => {
//                 // TODO: recurse into the function
//                 println!("WARN: not recursing into method call {}", path.join("."));
//                 let a = args
//                     .iter()
//                     .flat_map(|s| s.get_state_interface_references(prefix))
//                     .collect::<Vec<String>>();
//                 let mut s = HashSet::new();
//                 s.extend(a);
//                 s
//             }
//             Slice { path, slice, .. } => {
//                 let mut v = if path[0] == prefix {
//                     Expr::path_to_hashset(path)
//                 } else {
//                     HashSet::new()
//                 };
//                 v.extend(slice.get_state_interface_references(prefix));
//                 v
//             }
//             Element { path, idx, .. } => {
//                 if path[0] == prefix {
//                     let mut v = Expr::path_to_hashset(path);
//                     v.extend(idx.get_state_interface_references(prefix));
//                     v
//                 } else {
//                     HashSet::new()
//                 }
//             }
//             Range { start, end, .. } => {
//                 let mut v = start.get_state_interface_references(prefix);
//                 v.extend(end.get_state_interface_references(prefix));
//                 v
//             }
//             Quantifier { expr, .. } => expr.get_state_interface_references(prefix),
//         }
//     }

//     pub fn get_state_references(&self) -> HashSet<String> {
//         self.get_state_interface_references("state")
//     }

//     pub fn get_interface_references(&self) -> HashSet<String> {
//         self.get_state_interface_references("interface")
//     }

//     pub fn has_state_interface_references(&self, prefix: &str) -> bool {
//         use Expr::*;
//         match self {
//             Identifier { path, .. } => path[0] == prefix,
//             Number { .. } => false,
//             Boolean { .. } => false,
//             BinaryOperation { lhs, rhs, .. } => {
//                 lhs.has_state_interface_references(prefix)
//                     | rhs.has_state_interface_references(prefix)
//             }
//             UnaryOperation { val, .. } => val.has_state_interface_references(prefix),
//             FnCall { args, .. } => {
//                 for a in args {
//                     if a.has_state_interface_references(prefix) {
//                         return true;
//                     }
//                 }
//                 // TODO: recurse into the function
//                 false
//             }
//             Slice { path, slice, .. } => {
//                 (path[0] == prefix) | slice.has_state_interface_references(prefix)
//             }
//             Element { path, idx, .. } => {
//                 (path[0] == prefix) | idx.has_state_interface_references(prefix)
//             }
//             Range { start, end, .. } => {
//                 start.has_state_interface_references(prefix)
//                     | end.has_state_interface_references(prefix)
//             }
//             Quantifier { expr, .. } => expr.has_state_interface_references(prefix),
//         }
//     }

//     pub fn has_interface_references(&self) -> bool {
//         self.has_state_interface_references("interface")
//     }

//     pub fn has_state_references(&self) -> bool {
//         self.has_state_interface_references("state")
//     }

//     /// trying to split the expressions of the form `E and E`
//     pub fn split_and(self) -> Vec<Expr> {
//         match self {
//             Expr::BinaryOperation {
//                 lhs,
//                 rhs,
//                 op: BinOp::Land,
//                 ..
//             } => {
//                 // println!("Splitting: {}", self);
//                 let mut v = lhs.split_and();
//                 v.extend(rhs.split_and());
//                 v
//             }
//             _ => {
//                 vec![self]
//             }
//         }
//     }
// }

// impl Display for Expr {
//     fn fmt(&self, format: &mut fmt::Formatter) -> FmtResult {
//         use self::Expr::*;
//         match self {
//             Identifier { path, .. } => write!(format, "{}", path.join(".")),
//             Number { value, .. } => write!(format, "{}", value),
//             Boolean { value, .. } => write!(format, "{}", value),
//             BinaryOperation { op, lhs, rhs, .. } => write!(format, "({} {} {})", lhs, op, rhs),
//             UnaryOperation { op, val, .. } => write!(format, "{}({})", op, val),
//             FnCall { path, .. } => write!(format, "{}()", path.join(".")),
//             Slice { path, slice, .. } => write!(format, "{}[{}]", path.join("."), slice),
//             Element { path, idx, .. } => write!(format, "{}[{}]", path.join("."), idx),
//             Range { start, end, .. } => write!(format, "{}..{}", start, end),
//             Quantifier { kind, expr, .. } => write!(format, "{} {}", kind, expr),
//         }
//     }
// }

// impl<'a> AstNodeGeneric<'a> for Expr {
//     fn name(&self) -> &str {
//         "Expression"
//     }

//     /// performs teh ast check on the expression node
//     fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
//         let mut res = Issues::ok();

//         // Check 1: Sybol definitions
//         // --------------------------------------------------------------------------------------
//         // Type:        Error
//         // Description: Check that the symbols are defined
//         // Notes:
//         // --------------------------------------------------------------------------------------

//         res = res + self.check_symbols(st);

//         // Check 2: Type checks
//         // --------------------------------------------------------------------------------------
//         // Type:        Error
//         // Description: Check that teh types match
//         // Notes:
//         // --------------------------------------------------------------------------------------

//         res + self.check_types(st)
//     }

//     /// returns the location of the current
//     fn loc(&self) -> &TokenStream {
//         use self::Expr::*;
//         match &self {
//             Identifier { pos, .. } => pos,
//             Number { pos, .. } => pos,
//             Boolean { pos, .. } => pos,
//             BinaryOperation { pos, .. } => pos,
//             UnaryOperation { pos, .. } => pos,
//             FnCall { pos, .. } => pos,
//             Slice { pos, .. } => pos,
//             Element { pos, .. } => pos,
//             Range { pos, .. } => pos,
//             Quantifier { pos, .. } => pos,
//         }
//     }
// }

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
