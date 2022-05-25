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

mod actions;
mod bitslice;
mod consts;
mod expression;
mod field;
mod flags;
mod import;
mod interface;
mod issues;
mod map;
mod method;
mod param;
mod root;
mod state;
mod statement;
mod symboltable;
mod types;
mod unit;
mod utils;

use custom_error::custom_error;

use crate::parser::ParsErr;
use crate::token::{TokenStream, TOKENSTREAM_DUMMY};

// custom error definitions
custom_error! {#[derive(PartialEq)] pub AstError
    SymTabInsertExists        = "The symbol could not be inserted, already exists",
    SymTableNotExists         = "The symbol does not exist in the table",
    SymTabError{i: Issues}    = "There was an error during creating the symbol table",
    ImportError{e:ParsErr}    = "The parser has failed",
    DeriveError{i: Issues}     = "The unit drivation has failed",
    MergeError{i: Issues}     = "Merging of the ast has failed",
    CheckError{i: Issues}     = "There were warnings or errors",
}

// rexports
pub use actions::{Action, ActionComponent, ActionType};
pub use bitslice::BitSlice;
pub use consts::{Const, ConstValue};
pub use expression::{BinOp, Expr, Quantifier, UnOp};
pub use field::Field;
pub use flags::{Flag, Flags};
pub use import::Import;
pub use interface::{Interface, InterfaceField, NONE_INTERFACE};
pub use issues::Issues;
pub use map::{ExplicitMap, ListComprehensionMap, Map, MapEntry};
pub use method::Method;
pub use param::Param;
pub use root::AstRoot;
pub use state::{State, NONE_STATE};
pub use statement::Stmt;
pub use symboltable::{Symbol, SymbolKind, SymbolTable};
pub use types::Type;
pub use unit::{Segment, StaticMap, Unit, CFG_DEFAULT_BITWIDTH};

/// Trait that checks the Ast nodes for consistency
///
/// This trait has to be implemented by all the nodes. It provides common functionality
/// for the AstNodeGenerics, that is useful when printing error messages, for instance.
pub trait AstNodeGeneric<'a> {
    // checks the node and returns the number of errors encountered
    fn check(&'a self, _st: &mut SymbolTable<'a>) -> Issues {
        Issues::ok()
    }

    // reqrite the ast
    fn rewrite(&'a mut self, _st: &mut SymbolTable<'a>) {
        // no-op
    }

    /// returns a printable string representing the ast node
    fn name(&self) -> &str;

    /// returns the location of the AstNodeGeneric
    fn loc(&self) -> &TokenStream {
        &TOKENSTREAM_DUMMY
    }
}

/// enum of all AstNodes
#[derive(Clone)]
pub enum AstNode<'a> {
    Root(&'a AstRoot),
    Import(&'a Import),
    Const(&'a Const),
    Unit(&'a Unit),
    Segment(&'a Segment),
    StaticMap(&'a StaticMap),

    // state
    State(&'a State),
    Field(&'a Field),
    BitSlice(&'a BitSlice),

    // interface
    Interface(&'a Interface),
    InterfaceField(&'a InterfaceField),

    // map
    Map(&'a Map),

    // methods
    Method(&'a Method),
    Parameter(&'a Param),
    Statement(&'a Stmt),
    Expression(&'a Expr),
}

impl<'a> AstNodeGeneric<'a> for AstNode<'a> {
    /// returns a printable string representing the ast node
    fn name(&self) -> &str {
        match self {
            AstNode::Root(x) => x.name(),
            AstNode::Import(x) => x.name(),
            AstNode::Const(x) => x.name(),
            AstNode::Unit(x) => x.name(),
            AstNode::Segment(x) => x.name(),
            AstNode::StaticMap(x) => x.name(),
            AstNode::State(x) => x.name(),
            AstNode::Field(x) => x.name(),
            AstNode::BitSlice(x) => x.name(),
            AstNode::Interface(x) => x.name(),
            AstNode::InterfaceField(x) => x.name(),
            AstNode::Map(x) => x.name(),
            AstNode::Method(x) => x.name(),
            AstNode::Parameter(x) => x.name(),
            AstNode::Statement(x) => x.name(),
            AstNode::Expression(x) => x.name(),
        }
    }

    /// returns the location of the AstNodeGeneric
    fn loc(&self) -> &TokenStream {
        match self {
            AstNode::Root(x) => x.loc(),
            AstNode::Import(x) => x.loc(),
            AstNode::Const(x) => x.loc(),
            AstNode::Unit(x) => x.loc(),
            AstNode::Segment(x) => x.loc(),
            AstNode::StaticMap(x) => x.loc(),
            AstNode::State(x) => x.loc(),
            AstNode::Field(x) => x.loc(),
            AstNode::BitSlice(x) => x.loc(),
            AstNode::Interface(x) => x.loc(),
            AstNode::InterfaceField(x) => x.loc(),
            AstNode::Map(x) => x.loc(),
            AstNode::Method(x) => x.loc(),
            AstNode::Parameter(x) => x.loc(),
            AstNode::Statement(x) => x.loc(),
            AstNode::Expression(x) => x.loc(),
        }
    }
}
