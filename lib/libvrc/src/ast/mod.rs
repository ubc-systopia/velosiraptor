// Velosiraptor Lexer
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

//! # Ast Module of the Velosiraptor Compiler
//!
//! This module contains the abstract syntax tree representation produced by the parser from
//! a given input in the Velosiraptor Specification Language format.
//!
//! # Node Types
//!
//! The AST node contsists of the following distinct node types:
//!
//!  * Ast
//!  * Import
//!  * Constants
//!  * Units
//!  * Interface
//!  * Methods
//!  * State
//!  * Expressions
//!  * Fields
//!  * BitSlice

mod ast;
mod bitslice;
mod consts;
mod expression;
mod field;
mod import;
mod interface;
mod method;
mod state;
mod types;
mod unit;
mod utils;

pub mod symboltable;
pub mod transform;

use custom_error::custom_error;

use crate::parser::ParsErr;
use crate::token::TokenStream;

// custom error definitions
custom_error! {#[derive(PartialEq)] pub AstError
    SymTabInsertExists         = "The symbol could not be inserted, already exists",
    SymTableNotExists          = "The symbol does not exist in the table",
    ImportError{e:ParsErr} = "The parser has failed",
    MergeError{i: Issues} = "Merging of the ast has failed",
    CheckError{i: Issues} = "There were warnings or errors",
}

// rexports
pub use ast::Ast;
pub use bitslice::BitSlice;
pub use consts::Const;
pub use expression::{BinOp, Expr, UnOp};
pub use field::Field;
pub use import::Import;
pub use interface::Interface;
pub use method::Method;
pub use method::Stmt;
pub use state::State;
pub use types::Type;
pub use unit::Unit;


/// Trait that checks the Ast nodes for consistency
///
/// This trait has to be implemented by all the nodes
pub trait AstNode {
    // checks the node and returns the number of errors and warnings encountered
    fn check(&self) -> Issues {
        Issues::ok()
    }
    fn name(&self) -> &str;
    /// returns the location of the current
    fn loc(&self) -> &TokenStream;
}

#[derive(Debug, PartialEq)]
pub struct Issues {
    pub errors: u32,
    pub warnings: u32,
}

impl Issues {
    pub fn new(errors: u32, warnings: u32) -> Self {
        Issues { errors, warnings }
    }
    pub fn ok() -> Self {
        Issues {
            errors: 0,
            warnings: 0,
        }
    }
    pub fn warn() -> Self {
        Issues {
            errors: 0,
            warnings: 1,
        }
    }
    pub fn err() -> Self {
        Issues {
            errors: 1,
            warnings: 0,
        }
    }

    pub fn inc_err(&mut self, c: u32) {
        self.errors += c;
    }

    pub fn inc_warn(&mut self, c: u32) {
        self.warnings += c;
    }
}

impl std::fmt::Display for Issues {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "errors: {}  warnings: {}", self.errors, self.warnings)
    }
}

impl std::ops::Add for Issues {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self {
            warnings: self.warnings + other.warnings,
            errors: self.errors + other.errors,
        }
    }
}
