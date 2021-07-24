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

///! Ast Module of the Velosiraptor Compiler
use std::fmt;

use crate::ast::AstNode;
use crate::token::TokenStream;

/// Binary operations for [Expr] <OP> [Expr]
#[derive(Debug, PartialEq, Clone, Copy)]
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

impl BinOp {
    pub fn eval(&self, lhs: Expr, rhs: Expr, pos: TokenStream) -> Expr {
        use BinOp::*;
        use Expr::*;
        match (self, lhs, rhs) {
            // arithmetics
            (Plus, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Number {
                value: v1 + v2,
                pos,
            },
            (Minus, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Number {
                value: v1 - v2,
                pos,
            },
            (Multiply, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Number {
                value: v1 * v2,
                pos,
            },
            (Divide, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Number {
                value: v1 / v2,
                pos,
            },
            (Modulo, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Number {
                value: v1 % v2,
                pos,
            },
            (LShift, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Number {
                value: v1 << v2,
                pos,
            },
            (RShift, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Number {
                value: v1 >> v2,
                pos,
            },
            (And, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Number {
                value: v1 & v2,
                pos,
            },
            (Xor, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Number {
                value: v1 ^ v2,
                pos,
            },
            (Or, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Number {
                value: v1 | v2,
                pos,
            },
            // comparisons
            (Eq, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Boolean {
                value: v1 == v2,
                pos,
            },
            (Ne, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Boolean {
                value: v1 != v2,
                pos,
            },
            (Lt, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Boolean {
                value: v1 < v2,
                pos,
            },
            (Gt, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Boolean {
                value: v1 > v2,
                pos,
            },
            (Le, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Boolean {
                value: v1 <= v2,
                pos,
            },
            (Ge, Number { value: v1, pos: _ }, Number { value: v2, pos: _ }) => Boolean {
                value: v1 >= v2,
                pos,
            },
            // booleans
            (Land, Boolean { value: v1, pos: _ }, Boolean { value: v2, pos: _ }) => Boolean {
                value: v1 && v2,
                pos,
            },
            (Lor, Boolean { value: v1, pos: _ }, Boolean { value: v2, pos: _ }) => Boolean {
                value: v1 || v2,
                pos,
            },
            (Eq, Boolean { value: v1, pos: _ }, Boolean { value: v2, pos: _ }) => Boolean {
                value: v1 == v2,
                pos,
            },
            (Ne, Boolean { value: v1, pos: _ }, Boolean { value: v2, pos: _ }) => Boolean {
                value: v1 != v2,
                pos,
            },
            // can't handle this
            (_, lhs, rhs) => BinaryOperation {
                op: *self,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                pos,
            },
        }
    }
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

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum UnOp {
    // arithmetic operators
    Not,
    Ref,
    // boolean operator
    LNot,
}

impl UnOp {
    pub fn eval(&self, val: Expr, pos: TokenStream) -> Expr {
        use Expr::*;
        use UnOp::*;
        match (self, val) {
            (LNot, Boolean { value, pos: _ }) => Boolean { value: !value, pos },
            (Not, Number { value, pos: _ }) => Number { value: !value, pos },
            (_, val) => UnaryOperation {
                op: *self,
                val: Box::new(val),
                pos,
            },
        }
    }
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
        pos: TokenStream,
    },
    Number {
        value: u64,
        pos: TokenStream,
    },
    Boolean {
        value: bool,
        pos: TokenStream,
    },
    BinaryOperation {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        pos: TokenStream,
    },
    UnaryOperation {
        op: UnOp,
        val: Box<Expr>,
        pos: TokenStream,
    },
    FnCall {
        path: Vec<String>,
        args: Vec<String>,
        pos: TokenStream,
    },
    Slice {
        path: Vec<String>,
        slice: Box<Expr>,
        pos: TokenStream,
    },
    Element {
        path: Vec<String>,
        idx: Box<Expr>,
        pos: TokenStream,
    },
    Range {
        start: Box<Expr>,
        end: Box<Expr>,
        pos: TokenStream,
    },
}

impl Expr {
    /// returns ture if the expression is a constant expression
    pub fn is_const_expr(&self) -> bool {
        use Expr::*;
        match self {
            Number { value: _, pos: _ } => true,
            Boolean { value: _, pos: _ } => true,
            BinaryOperation {
                op: _,
                lhs,
                rhs,
                pos: _,
            } => lhs.is_const_expr() && rhs.is_const_expr(),
            UnaryOperation { op: _, val, pos: _ } => val.is_const_expr(),
            _ => false,
        }
    }

    pub fn fold_constants(self) -> Self {
        use Expr::*;
        match self {
            BinaryOperation { op, lhs, rhs, pos } => {
                let lhs = lhs.fold_constants();
                let rhs = rhs.fold_constants();
                op.eval(lhs, rhs, pos)
            }
            UnaryOperation { op, val, pos } => {
                let val = val.fold_constants();
                op.eval(val, pos)
            }
            Slice { path, slice, pos } => {
                let slice = slice.fold_constants();
                Slice {
                    path,
                    slice: Box::new(slice),
                    pos,
                }
            }
            Element { path, idx, pos } => {
                let idx = idx.fold_constants();
                Element {
                    path,
                    idx: Box::new(idx),
                    pos,
                }
            }
            id => id,
        }
    }
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
            FnCall {
                path,
                pos: _,
                args: _,
            } => {
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

impl AstNode for Expr {
    fn name(&self) -> &str {
        "Expression"
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        use self::Expr::*;
        match &self {
            Identifier { path: _, pos } => &pos,
            Number { value: _, pos } => &pos,
            Boolean { value: _, pos } => &pos,
            BinaryOperation {
                op: _,
                lhs: _,
                rhs: _,
                pos,
            } => &pos,
            UnaryOperation { op: _, val: _, pos } => &pos,
            FnCall {
                path: _,
                pos,
                args: _,
            } => &pos,
            Slice {
                path: _,
                slice: _,
                pos,
            } => &pos,
            Element {
                path: _,
                idx: _,
                pos,
            } => &pos,
            Range {
                start: _,
                end: _,
                pos,
            } => &pos,
        }
    }
}

#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::parser::{arith_expr, bool_expr};
#[cfg(test)]
use crate::sourcepos::SourcePos;

#[cfg(test)]
macro_rules! parse_equal (
    ($parser:expr, $lhs:expr, $rhs:expr) => (
        let sp = SourcePos::new("stdio", $lhs);
        let tokens = Lexer::lex_source_pos(sp).unwrap();
        let ts = TokenStream::from_vec(tokens);
        let (_, ex) = $parser(ts.clone()).unwrap();
        assert_eq!(
            format!("{}", ex.fold_constants()),
            String::from($rhs)
        );
    )
);

#[test]
fn const_folding_test() {
    parse_equal!(arith_expr, "1+3", "4");
    parse_equal!(arith_expr, "1+3*4", "13");
    parse_equal!(bool_expr, "true && false", "false");
    parse_equal!(bool_expr, "true || false", "true");
    //assert_eq!(ex.map(|(i, x)| (i, format!("{}", x))), String::from("4"));
}
