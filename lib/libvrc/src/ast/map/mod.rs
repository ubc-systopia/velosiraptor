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

mod explicit;
mod list;

pub use explicit::ExplicitMap;
pub use list::ListComprehensionMap;

/// Defines a mapping between addresses and units
#[derive(PartialEq, Debug, Clone)]
pub enum Map {
    /// explicit map
    Explicit(ExplicitMap),
    /// list comprehension map
    ListComprehension(ListComprehensionMap),
}

impl Map {}

/// Implementation of [AstNodeGeneric] for [Map]
impl<'a> AstNodeGeneric<'a> for Map {
    // checks the node and returns the number of errors and warnings encountered
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        match self {
            Map::Explicit(map) => map.check(st),
            Map::ListComprehension(map) => map.check(st),
        }
    }

    /// rewrite the ast
    fn rewrite(&'a mut self, st: &mut SymbolTable<'a>) {
        match self {
            Map::Explicit(map) => map.rewrite(st),
            Map::ListComprehension(map) => map.rewrite(st),
        };
    }

    /// returns a printable string representation of the ast node
    fn name(&self) -> &str {
        match self {
            Map::Explicit(map) => map.name(),
            Map::ListComprehension(map) => map.name(),
        }
    }

    /// returns the location of the AstNodeGeneric
    fn loc(&self) -> &TokenStream {
        match self {
            Map::Explicit(map) => map.loc(),
            Map::ListComprehension(map) => map.loc(),
        }
    }
}

/// Defines an entry in the [StaticMap] unit
///
/// The canonical form of a map entry is: `INPUT RANGE => Unit(arglist) @ offset`
/// where
///   - INPUT RANGE is optional
///   - arglist may be empty
///   - offset is optional
#[derive(PartialEq, Debug, Clone)]
pub struct MapEntry {
    /// range expressiong of the input address range that this entry maps
    pub range: Option<Expr>,
    /// the name of the unit this entry maps to
    pub unit_name: String,
    /// list of expressions to initialize the unit parameters
    pub unit_params: Vec<Expr>,
    /// offset into the unit
    pub offset: Option<Expr>,
    /// the position of the map in the source code
    pub pos: TokenStream,
}

impl MapEntry {
    pub fn new(pos: TokenStream, unit: String) -> Self {
        Self {
            range: None,
            unit_name: unit,
            unit_params: vec![],
            offset: None,
            pos,
        }
    }

    pub fn set_range(mut self, range: Option<Expr>) -> Self {
        self.range = range;
        self
    }

    pub fn add_unit_param(mut self, param: Expr) -> Self {
        self.unit_params.push(param);
        self
    }

    pub fn add_unit_params(mut self, params: Vec<Expr>) -> Self {
        self.unit_params.extend(params);
        self
    }

    pub fn set_offset(mut self, offset: Option<Expr>) -> Self {
        self.offset = offset;
        self
    }

    pub fn finalize(mut self, pos: &TokenStream) -> Self {
        self.pos = self.pos.expand_until(pos);
        self
    }
}

/// Implementation of [AstNodeGeneric] for [Map]
impl<'a> AstNodeGeneric<'a> for MapEntry {
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
        "mapentry"
    }

    /// returns the location of the AstNodeGeneric
    fn loc(&self) -> &TokenStream {
        &self.pos
    }
}
