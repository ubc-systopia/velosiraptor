// Velosiraptor ParseTree
//
//
// MIT License
//
// Copyright (c) 2021 Systopia Lab, Computer Science, University of British Columbia
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

use crate::sourcepos::SourcePos;
///! Ast Module of the Velosiraptor Compiler
use std::fmt;

/// Binary operations for [Expr] <OP> [Expr]
#[derive(Debug, PartialEq, Clone)]
pub enum BinOp {
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
}

impl fmt::Display for BinOp {
    fn fmt(&self, format: &mut fmt::Formatter) -> fmt::Result {
        use self::BinOp::*;
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
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum UnOp {
    // arithmetic operators
    Not,
    Ref,
    // boolean operator
    LNot,
}

impl fmt::Display for UnOp {
    fn fmt(&self, format: &mut fmt::Formatter) -> fmt::Result {
        use self::UnOp::*;
        match self {
            Not => write!(format, "~"),
            LNot => write!(format, "!"),
            Ref => write!(format, "&"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Identifier {
        path: Vec<String>,
        pos: SourcePos,
    },
    Number {
        value: u64,
        pos: SourcePos,
    },
    Boolean {
        value: bool,
        pos: SourcePos,
    },
    BinaryOperation {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        pos: SourcePos,
    },
    UnaryOperation {
        op: UnOp,
        val: Box<Expr>,
        pos: SourcePos,
    },
    FnCall {
        path: Vec<String>,
        pos: SourcePos,
    },
    Slice {
        path: Vec<String>,
        slice: Box<Expr>,
        pos: SourcePos,
    },
    Element {
        path: Vec<String>,
        idx: Box<Expr>,
        pos: SourcePos,
    },
    Range {
        start: Box<Expr>,
        end: Box<Expr>,
        pos: SourcePos,
    },
}

impl fmt::Display for Expr {
    fn fmt(&self, format: &mut fmt::Formatter) -> fmt::Result {
        use self::Expr::*;
        match self {
            Identifier { path, pos: _ } => write!(format, "{}", path.join(".")),
            Number { value, pos: _ } => write!(format, "{}", value),
            Boolean { value, pos: _ } => write!(format, "{}", value),
            BinaryOperation {
                op,
                lhs,
                rhs,
                pos: _,
            } => write!(format, "({} {} {})", lhs, op, rhs),
            UnaryOperation { op, val, pos: _ } => write!(format, "{}({})", op, val),
            FnCall { path, pos: _ } => {
                write!(format, "{}()", path.join("."))
            }
            Slice {
                path,
                slice,
                pos: _,
            } => write!(format, "{}[{}]", path.join("."), slice),
            Element { path, idx, pos: _ } => {
                write!(format, "{}[{}]", path.join("."), idx)
            }
            Range { start, end, pos: _ } => write!(format, "{}..{}", start, end),
        }
    }
}
