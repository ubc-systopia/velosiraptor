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

//! Ast Module of the Velosiraptor Compiler

use crate::ast::Ast;
use crate::sourcepos::SourcePos;
use std::fmt;

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
    pub pos: SourcePos,
}

/// implementation of the [fmt::Display] trait for the [Import]
impl fmt::Display for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "import {};", self.name)
    }
}

/// implementation of the [fmt::Debug] trait for the [Import]
impl fmt::Debug for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.pos.input_pos();
        writeln!(f, "{:03}:{:03} | import {};", line, column, self.name)
    }
}
