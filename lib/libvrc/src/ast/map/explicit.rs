// Velosiraptor Parser
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

//! MAP ast node

use crate::ast::{AstNodeGeneric, Issues, SymbolTable};
use crate::token::TokenStream;

use super::MapEntry;

/// Represents an explicit map `map = [0x0...0x1000 => Unit(args) @ offset, ... ]`
#[derive(PartialEq, Debug, Clone)]
pub struct ExplicitMap {
    /// the entries in the explicit map
    pub entries: Vec<MapEntry>,
    /// the position of the map in the source code
    pub pos: TokenStream,
}

impl ExplicitMap {
    pub fn new(pos: TokenStream) -> Self {
        Self {
            entries: Vec::new(),
            pos,
        }
    }

    pub fn add_entry(&mut self, entry: MapEntry) {
        self.entries.push(entry);
    }

    pub fn add_entries(mut self, entries: Vec<MapEntry>) -> Self {
        self.entries.extend(entries);
        self
    }

    pub fn finalize(mut self, pos: &TokenStream) -> Self {
        self.pos = self.pos.expand_until(pos);
        self
    }
}

/// Implementation of [AstNodeGeneric] for [ExplicitMap]
impl<'a> AstNodeGeneric<'a> for ExplicitMap {
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
