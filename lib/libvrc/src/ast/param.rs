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

///! Param Module
// std lib imports
use std::fmt;

use crate::ast::{AstNode, AstNodeGeneric, Issues, Symbol, SymbolKind, SymbolTable, Type};
use crate::token::TokenStream;

/// Defines a Method inside a unit
#[derive(PartialEq, Clone)]
pub struct Param {
    /// the name of the method
    pub name: String,
    /// the return type of the method
    pub ptype: Type,
    /// the position where the method was defined
    pub pos: TokenStream,
}

/// implementation of the [Param] ast node
impl Param {
    /// returns a new parameter without any associated TokenStream
    pub fn new(name: String, ptype: Type) -> Self {
        Param {
            name,
            ptype,
            pos: TokenStream::empty(),
        }
    }

    /// creates a new symbol from the parameter
    pub fn to_symbol(&self) -> Symbol {
        Symbol {
            kind: SymbolKind::Parameter,
            name: self.name.clone(),
            typeinfo: self.ptype,
            loc: self.pos.clone(),
            ast_node: AstNode::Parameter(self),
        }
    }
}

/// Implementation of the [fmt::Display] trait for [Param]
impl fmt::Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{} : {}", self.name, self.ptype)
    }
}

/// Implementation of the [fmt::Display] trait for [Param]
impl fmt::Debug for Param {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{} : {}", self.name, self.ptype)
    }
}

/// implementation of [AstNodeGeneric] for [Method]
impl<'a> AstNodeGeneric<'a> for Param {
    // performs checks on the parameter
    fn check(&self, _st: &mut SymbolTable) -> Issues {
        Issues::ok()
    }

    /// returns the name of the parameter
    fn name(&self) -> &str {
        &self.name
    }

    /// returns the location of the parameter
    fn loc(&self) -> &TokenStream {
        &self.pos
    }
}
