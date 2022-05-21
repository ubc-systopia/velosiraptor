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

use crate::ast::{AstNodeGeneric, Expr, Issues, SymbolTable};
use crate::token::TokenStream;

/// Defines a mapping between addresses and units
#[derive(PartialEq, Debug, Clone)]
pub struct Map {
    pub entries: Vec<MapEntry>,
    pub pos: TokenStream,
}

impl Map {
    pub fn new(pos: TokenStream) -> Self {
        Map {
            entries: Vec::new(),
            pos,
        }
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

/// Implementation of [AstNodeGeneric] for [Map]
impl<'a> AstNodeGeneric<'a> for Map {
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

/// Defines the parameters for constructing a Unit as a component
/// of a given map
/// TODO:
///     Might need to add an AstNodeGeneric Trait Implementation for
///     the MapEntry struct
#[derive(Default, PartialEq, Debug, Clone)]
pub struct MapEntry {
    pub range: Option<Expr>,
    pub unit_name: String,
    pub unit_params: Vec<Expr>,
    pub offset: Option<Expr>,
    pub iteration: Option<(String, u64)>,
}
