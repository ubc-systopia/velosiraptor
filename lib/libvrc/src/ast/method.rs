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

///! Method module
// std lib imports
use std::fmt;

use crate::ast::{AstNode, Expr, Issues, Stmt, SymbolTable, Type};
use crate::token::TokenStream;

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
    /// the ensures clauses
    pub requires: Vec<Expr>,
    /// the ensures clauses
    pub ensures: Vec<Expr>,
    /// A sequence of statements
    pub stmts: Vec<Stmt>,
    /// the position where the method was defined
    pub pos: TokenStream,
}

impl Method {
    pub fn check_map(&self) -> Issues {
        Issues::ok()
    }
    pub fn check_translate(&self) -> Issues {
        Issues::ok()
    }
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
        let (line, column) = self.pos.input_sourcepos().input_pos();
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

/// implementation of [AstNode] for [Field]
impl AstNode for Method {
    fn check(&self, _st: &mut SymbolTable) -> Issues {
        Issues::ok()
    }

    fn name(&self) -> &str {
        &self.name
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        &self.pos
    }
}
