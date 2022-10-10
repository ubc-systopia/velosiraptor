// VelosiParser -- a parser for the Velosiraptor Language
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

//! # VelosiParser -- Parse Tree Expressions
//!
//! This module defines the expression nodes for the parse tree

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

// used crate functionality
use crate::VelosiTokenStream;

use crate::parsetree::VelosiParseTreeParam;

/// Represents an operator for a binary expression
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum VelosiParseTreeBinOp {
    // arithmetic opreators
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
    // boolean operators
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    Land,
    Lor,
    Implies,
}

/// Implementation of [Display] for [VelosiParseTreeBinOp]
impl Display for VelosiParseTreeBinOp {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        use VelosiParseTreeBinOp::*;
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

/// Represents a binary operation `expr <op> expr`
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeBinOpExpr {
    lhs: Box<VelosiParseTreeExpr>,
    op: VelosiParseTreeBinOp,
    rhs: Box<VelosiParseTreeExpr>,
    loc: VelosiTokenStream,
}

impl VelosiParseTreeBinOpExpr {
    pub fn new(
        lhs: VelosiParseTreeExpr,
        op: VelosiParseTreeBinOp,
        rhs: VelosiParseTreeExpr,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
            loc,
        }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        &self.loc
    }
}

/// Implementation of [Display] for [VelosiParseTreeBinOpExpr]
impl Display for VelosiParseTreeBinOpExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "({} {} {})", self.lhs, self.op, self.rhs)
    }
}

/// Represents an operator for a unary expression
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum VelosiParseTreeUnOp {
    // arithmetic operators
    Not,
    // boolean operator
    LNot,
}

/// Implementation of [Display] for [VelosiParseTreeUnOp]
impl Display for VelosiParseTreeUnOp {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        use VelosiParseTreeUnOp::*;
        match self {
            Not => write!(format, "~"),
            LNot => write!(format, "!"),
        }
    }
}

/// Represents an unary operation
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeUnOpExpr {
    op: VelosiParseTreeUnOp,
    expr: Box<VelosiParseTreeExpr>,
    loc: VelosiTokenStream,
}

impl VelosiParseTreeUnOpExpr {
    pub fn new(op: VelosiParseTreeUnOp, expr: VelosiParseTreeExpr, loc: VelosiTokenStream) -> Self {
        Self {
            op,
            expr: Box::new(expr),
            loc,
        }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        &self.loc
    }
}

/// Implementation of [Display] for [VelosiParseTreeUnOpExpr]
impl Display for VelosiParseTreeUnOpExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}({})", self.op, self.expr)
    }
}

/// representation of a quantifier
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VelosiParseTreeQuantifier {
    Forall,
    Exists,
}

/// Implementation of [Display] for [VelosiParseTreeQuantifier]
impl Display for VelosiParseTreeQuantifier {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        use VelosiParseTreeQuantifier::*;
        match self {
            Forall => write!(format, "forall"),
            Exists => write!(format, "exists"),
        }
    }
}

/// Represents an unary operation
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeQuantifierExpr {
    quant: VelosiParseTreeQuantifier,
    params: Vec<VelosiParseTreeParam>,
    expr: Box<VelosiParseTreeExpr>,
    loc: VelosiTokenStream,
}

impl VelosiParseTreeQuantifierExpr {
    pub fn new(
        quant: VelosiParseTreeQuantifier,
        params: Vec<VelosiParseTreeParam>,
        expr: VelosiParseTreeExpr,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            quant,
            params,
            expr: Box::new(expr),
            loc,
        }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        &self.loc
    }
}

/// Implementation of [Display] for [VelosiParseTreeQuantifierExpr]
impl Display for VelosiParseTreeQuantifierExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "({} |", self.quant)?;
        for (i, p) in self.params.iter().enumerate() {
            if i != 0 {
                write!(format, ", ")?;
            }
            write!(format, "{}", p)?;
        }
        write!(format, " :: {})", self.expr)
    }
}

/// Represents an unary operation
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeIdentifierLiteral {
    path: Vec<String>,
    loc: VelosiTokenStream,
}

impl VelosiParseTreeIdentifierLiteral {
    pub fn new(path: Vec<String>, loc: VelosiTokenStream) -> Self {
        Self { path, loc }
    }
    pub fn loc(&self) -> &VelosiTokenStream {
        &self.loc
    }
}

/// Implementation of [Display] for [VelosiParseTreeIdentifierLiteral]
impl Display for VelosiParseTreeIdentifierLiteral {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        for (i, p) in self.path.iter().enumerate() {
            if i != 0 {
                write!(format, ".")?;
            }
            write!(format, "{}", p)?;
        }
        Ok(())
    }
}

/// Represents an unary operation
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeNumLiteral {
    value: u64,
    loc: VelosiTokenStream,
}

impl VelosiParseTreeNumLiteral {
    pub fn new(value: u64, loc: VelosiTokenStream) -> Self {
        Self { value, loc }
    }
    pub fn loc(&self) -> &VelosiTokenStream {
        &self.loc
    }
}

/// Implementation of [Display] for [VelosiParseTreeNumLiteral]
impl Display for VelosiParseTreeNumLiteral {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}", self.value)
    }
}

/// Represents an unary operation
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeBoolLiteral {
    value: bool,
    loc: VelosiTokenStream,
}

impl VelosiParseTreeBoolLiteral {
    pub fn new(value: bool, loc: VelosiTokenStream) -> Self {
        Self { value, loc }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        &self.loc
    }
}

/// Implementation of [Display] for [VelosiParseTreeBoolLiteral]
impl Display for VelosiParseTreeBoolLiteral {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}", self.value)
    }
}

/// Represents an unary operation
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeFnCallExpr {
    path: VelosiParseTreeIdentifierLiteral,
    args: Vec<VelosiParseTreeExpr>,
    loc: VelosiTokenStream,
}

impl VelosiParseTreeFnCallExpr {
    pub fn new(
        path: VelosiParseTreeIdentifierLiteral,
        args: Vec<VelosiParseTreeExpr>,
        loc: VelosiTokenStream,
    ) -> Self {
        Self { path, args, loc }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        &self.loc
    }
}

/// Implementation of [Display] for [VelosiParseTreeFnCallExpr]
impl Display for VelosiParseTreeFnCallExpr {
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

/// Represents an unary operation
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeIfElseExpr {
    cond: Box<VelosiParseTreeExpr>,
    then: Box<VelosiParseTreeExpr>,
    other: Box<VelosiParseTreeExpr>,
    loc: VelosiTokenStream,
}

impl VelosiParseTreeIfElseExpr {
    pub fn new(
        cond: VelosiParseTreeExpr,
        then: VelosiParseTreeExpr,
        other: VelosiParseTreeExpr,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            cond: Box::new(cond),
            then: Box::new(then),
            other: Box::new(other),
            loc,
        }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        &self.loc
    }
}

/// Implementation of [Display] for [VelosiParseTreeIfElseExpr]
impl Display for VelosiParseTreeIfElseExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(
            format,
            "if {} {{ {} }} else {{ {} }}",
            self.cond, self.then, self.other
        )
    }
}

/// Represents an expression in the parse tree
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiParseTreeExpr {
    Identifier(VelosiParseTreeIdentifierLiteral),
    NumLiteral(VelosiParseTreeNumLiteral),
    BoolLiteral(VelosiParseTreeBoolLiteral),
    BinOp(VelosiParseTreeBinOpExpr),
    UnOp(VelosiParseTreeUnOpExpr),
    Quantifier(VelosiParseTreeQuantifierExpr),
    FnCall(VelosiParseTreeFnCallExpr),
    IfElse(VelosiParseTreeIfElseExpr),
}

impl VelosiParseTreeExpr {
    pub fn loc(&self) -> &VelosiTokenStream {
        use VelosiParseTreeExpr::*;
        match self {
            Identifier(i) => i.loc(),
            NumLiteral(i) => i.loc(),
            BoolLiteral(i) => i.loc(),
            BinOp(i) => i.loc(),
            UnOp(i) => i.loc(),
            Quantifier(i) => i.loc(),
            FnCall(i) => i.loc(),
            IfElse(i) => i.loc(),
        }
    }
}

/// Implementation of [Display] for [VelosiParseTreeExpr]
impl Display for VelosiParseTreeExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        match self {
            VelosiParseTreeExpr::Identifier(i) => Display::fmt(&i, format),
            VelosiParseTreeExpr::NumLiteral(i) => Display::fmt(&i, format),
            VelosiParseTreeExpr::BoolLiteral(i) => Display::fmt(&i, format),
            VelosiParseTreeExpr::BinOp(i) => Display::fmt(&i, format),
            VelosiParseTreeExpr::UnOp(i) => Display::fmt(&i, format),
            VelosiParseTreeExpr::Quantifier(i) => Display::fmt(&i, format),
            VelosiParseTreeExpr::FnCall(i) => Display::fmt(&i, format),
            VelosiParseTreeExpr::IfElse(i) => Display::fmt(&i, format),
        }
    }
}
