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

use crate::ast::{AstNodeGeneric, Expr, Issues, SymbolTable};
use crate::token::TokenStream;

use super::MapEntry;

/// Represents a list comprehension map `map = [Unit(args) @ offset for x in 0..1024]`
#[derive(PartialEq, Debug, Clone)]
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

/// Implementation of [AstNodeGeneric] for [Map]
impl<'a> AstNodeGeneric<'a> for ListComprehensionMap {
    // checks the node and returns the number of errors and warnings encountered
    fn check(&self, _st: &mut SymbolTable) -> Issues {
        todo!()
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
