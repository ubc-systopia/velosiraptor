// Velosiraptor Parser
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! MAP ast node

// std library imports
use std::fmt::{Debug, Display, Formatter, Result};

use crate::ast::{
    utils, AstNode, AstNodeGeneric, Expr, Issues, Symbol, SymbolKind, SymbolTable, Type,
};
use crate::error::{ErrorLocation, VrsError};
use crate::token::TokenStream;

use super::MapEntry;

/// Represents a list comprehension map `map = [Unit(args) @ offset for x in 0..1024]`
#[derive(PartialEq, Clone)]
pub struct ListComprehensionMap {
    /// the entries in the explicit map
    pub entry: MapEntry,

    /// the iterator variable
    pub var: String,

    /// the possible range the variable [var] may take
    pub range: Expr,

    /// the position of the map in the source code
    pub pos: TokenStream,
}

impl ListComprehensionMap {
    pub fn new(entry: MapEntry, var: String, range: Expr, pos: TokenStream) -> Self {
        ListComprehensionMap {
            entry,
            var,
            range,
            pos,
        }
    }

    pub fn set_entry(mut self, entry: MapEntry) -> Self {
        self.entry = entry;
        self
    }

    pub fn set_var(mut self, var: String) -> Self {
        self.var = var;
        self
    }

    pub fn set_range(mut self, range: Expr) -> Self {
        self.range = range;
        self
    }

    pub fn finalize(mut self, pos: &TokenStream) -> Self {
        self.pos = self.pos.expand_until(pos);
        self
    }
}

/// implementation of the [fmt::Display] trait for the [Segment]
impl Display for ListComprehensionMap {
    fn fmt(&self, f: &mut Formatter) -> Result {
        writeln!(
            f,
            "map = [{} for {} in {}]",
            self.entry, self.var, self.range
        )
    }
}

/// implementation of the [fmt::Debug] trait for the [Segment]
impl Debug for ListComprehensionMap {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let line = self.loc().line();
        let column = self.loc().column();

        writeln!(
            f,
            "{:03}:{:03} | map = [{} for {} in {}]",
            line, column, self.entry, self.var, self.range
        )
    }
}

/// Implementation of [AstNodeGeneric] for [Map]
impl<'a> AstNodeGeneric<'a> for ListComprehensionMap {
    // checks the node and returns the number of errors and warnings encountered
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        // all fine for now
        let mut res = Issues::ok();

        // set the current context
        st.create_context(String::from("listcomprehension"));

        // Check 1: Check the range expression for defined symbols
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that the range expression is well-defined
        // Notes:       We need to do this *before* we add the variable to the symbol table
        // --------------------------------------------------------------------------------------

        if let Expr::Range { .. } = &self.range {
            // check the range expression
            res = res + self.range.check(st);
        } else {
            let msg = String::from("expression is not a range expression.");
            let hint =
                String::from("convert exprssion into a range expression of format `start..end`");
            VrsError::new_err(self.pos.clone(), msg, Some(hint)).print();
            res.inc_err(1);
        }

        // now add the iterator variable to the symbol table

        let varsym = Symbol::new(
            self.var.clone(),
            Type::Integer,
            SymbolKind::Variable,
            self.pos.clone(),
            AstNode::Expression(&self.range),
        );

        // try to insert the variable into the symbol table
        if !st.insert(varsym) {
            res.inc_err(1);
        }

        // Check 2: Check the entry for well-formedness
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that the entry is well-defined
        // Notes:
        // --------------------------------------------------------------------------------------
        res = res + self.entry.check(st);

        // Check 3: Variable name
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: Check if the unit name is snake case.
        // Notes:       --
        // --------------------------------------------------------------------------------------

        res = res + utils::check_snake_case(self.var.as_str(), &self.pos);

        // drop the context again
        st.drop_context();

        res
    }

    /// rewrite the ast
    fn rewrite(&mut self, _st: &mut SymbolTable) {
        // no-op
    }

    /// returns a printable string representation of the ast node
    fn name(&self) -> &str {
        "map"
    }

    /// returns the location of the AstNodeGeneric
    fn loc(&self) -> &TokenStream {
        &self.pos
    }
}
