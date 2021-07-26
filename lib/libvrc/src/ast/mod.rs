// Velosiraptor Ast
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
mod bitslice;
mod consts;
mod expression;
mod field;
mod import;
mod interface;
mod issues;
mod method;
mod state;
mod symboltable;
pub mod transform;
mod types;
mod unit;
mod utils;

use custom_error::custom_error;

use crate::parser::ParsErr;
use crate::token::TokenStream;

// custom error definitions
custom_error! {#[derive(PartialEq)] pub AstError
    SymTabInsertExists         = "The symbol could not be inserted, already exists",
    SymTableNotExists          = "The symbol does not exist in the table",
    SymTabError{i: Issues}    = "There was an error during creating the symbol table",
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
pub use issues::Issues;
pub use method::Method;
pub use method::Stmt;
pub use state::State;
pub use symboltable::{Symbol, SymbolKind, SymbolTable};
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
    // builds the symbol table
    fn build_symtab(&self, _ctxt: &mut Vec<String>, _st: &mut SymbolTable) -> Issues {
        Issues::ok()
    }

    fn name(&self) -> &str;
    /// returns the location of the current
    fn loc(&self) -> &TokenStream;
}
