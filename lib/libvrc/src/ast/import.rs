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

//! Import Ast Node
//!
//! This defines an import node in the AST. The import node represents the import
//! statements in the source files. They may contain the corresponding ast.

// the used standard library functionality
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter, Result};

// the used crate-internal functionality
use crate::ast::{Ast, AstNode};
use crate::token::TokenStream;

/// Defines an [Import] statement node
///
/// The import statement declares that another file is imported
/// and its definitions used by the current file.
#[derive(PartialEq, Clone)]
pub struct Import {
    /// the filename to import
    pub name: String,
    /// stores the ast at this import
    pub ast: Option<Ast>,
    /// where in the current file there was this import statement
    pub pos: TokenStream,
}

/// the implementation for the import struct
impl Import {
    /// returns the filename of the import by adding `*.vrs` to the name
    pub fn to_filename(&self) -> String {
        format!("{}.vrs", self.name)
    }
}

/// implementation of the [Display] trait for the [Import]
impl Display for Import {
    fn fmt(&self, f: &mut Formatter) -> Result {
        writeln!(f, "import {};", self.name)
    }
}

/// implementation of the [Debug] trait for the [Import]
impl Debug for Import {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let (line, column) = self.pos.peek().spos.input_pos();
        writeln!(f, "{:03}:{:03} | import {};", line, column, self.name)
    }
}

/// implementation of [PartialOrd] for [Import]
impl PartialOrd for Import {
    /// This method returns an ordering between self and other values if one exists.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // we jus compare with the TokenStream position
        self.pos.partial_cmp(&other.pos)
    }
}

/// implementation of [AstNode] for [Import]
impl AstNode for Import {
    // returns the name of the node
    fn name(&self) -> &str {
        &self.name
    }
    /// returns the location of the node, i.e. its [TokenStream]
    fn loc(&self) -> &TokenStream {
        &self.pos
    }
}
