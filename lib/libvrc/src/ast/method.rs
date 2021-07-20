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

///! Ast module
use std::fmt;

use crate::ast::{Expr, Type};
use crate::sourcepos::SourcePos;

/// Defines a Method inside a unit
///
/// A method defines certain functionality of the translation unit.
///
/// # Examples
///
///  - Translate(): a method that translates an address (required)
///  - get_size(): a method that extracts the
#[derive(PartialEq, Clone)]
pub struct Method {
    /// the name of the method
    pub name: String,
    /// the return type of the method
    pub rettype: Type,
    /// A list of arguments with their types
    pub args: Vec<(String, Type)>,
    /// A sequence of statements
    pub stmts: Vec<Stmt>,
    /// the position where the method was defined
    pub pos: SourcePos,
}

/// Implementation of the [fmt::Display] trait for [Field]
impl fmt::Display for Method {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "fn {}() -> {} {{", self.name, self.rettype)?;
        self.stmts.iter().fold(Ok(()), |result, s| {
            result.and_then(|_| writeln!(f, "  {}", s))
        })?;
        writeln!(f, "}}")
    }
}

/// Implementation of the [fmt::Debug] trait for [Field]
impl fmt::Debug for Method {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.pos.input_pos();
        writeln!(
            f,
            "{:03}:{:03} | fn {}() -> {} {{",
            line, column, self.name, self.rettype
        )?;
        self.stmts.iter().fold(Ok(()), |result, s| {
            result.and_then(|_| writeln!(f, "  {:?}", s))
        })?;
        writeln!(f, "}}")
    }
}

/// Represents a statement
#[derive(Debug, PartialEq, Clone)]
pub enum Stmt {
    /// a block is a sequence of statements
    Block { stmts: Vec<Stmt>, pos: SourcePos },
    /// the assign statements gives a name to a value
    Assign {
        typeinfo: Type,
        lhs: String,
        rhs: Expr,
        pos: SourcePos,
    },
    /// the conditional with
    IfElse {
        cond: Expr,
        then: Box<Stmt>,
        other: Option<Box<Stmt>>,
        pos: SourcePos,
    },
    /// assert statement
    Assert { expr: Expr, pos: SourcePos },
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Stmt::*;
        match self {
            Block { stmts, pos: _ } => {
                write!(f, "{{ TODO }} \n")
            }
            Assign {
                typeinfo,
                lhs,
                rhs,
                pos: _,
            } => write!(f, "let {} : {} = {};\n", typeinfo, lhs, rhs),
            Assert { expr, pos: _ } => write!(f, "assert {};", expr),
            IfElse {
                cond,
                then,
                other,
                pos: _,
            } => match other {
                None => write!(f, "if {} {} \n", cond, then),
                Some(x) => write!(f, "if {} {} else {} \n", cond, then, x),
            },
        }
    }
}
