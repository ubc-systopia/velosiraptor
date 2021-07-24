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

//! Ast Module of the Velosiraptor Compiler

mod ast;
mod consts;
mod expression;
mod import;
mod interface;
mod method;
mod state;
mod types;
mod unit;

pub mod symboltable;
pub mod transform;

use custom_error::custom_error;

use crate::parser::ParsErr;

// custom error definitions
custom_error! {#[derive(PartialEq)] pub AstError
    SymTabInsertExists         = "The symbol could not be inserted, already exists",
    SymTableNotExists          = "The symbol does not exist in the table",
    ImportError { error: ParsErr } = "The parser has failed",
    MergeError {  } = "Merging of the ast has failed"
}

// rexports
pub use ast::Ast;
pub use consts::Const;
pub use expression::{BinOp, Expr, UnOp};
pub use import::Import;
pub use interface::Interface;
pub use method::Method;
pub use method::Stmt;
pub use state::BitSlice;
pub use state::Field;
pub use state::State;
pub use types::Type;
pub use unit::Unit;

/// Trait that checks the Ast nodes for consistency
///
/// This trait has to be implemented by all the nodes
trait AstNode {
    fn check(&self) -> (u32, u32);
}
