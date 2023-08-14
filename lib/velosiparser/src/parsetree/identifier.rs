// VelosiParser -- a parser for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2021-2023 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiParser -- Identifier Node of the Parse Tree
//!
//! This module defines the identifier nodes of the parse tree.

// used standard library components
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

// use crate functionality
use crate::VelosiTokenStream;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Identifier Node
////////////////////////////////////////////////////////////////////////////////////////////////////

/// represents an identifier node in the parse tree
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeIdentifier {
    /// string representing the identifier
    pub name: String,
    /// location where the identifier was found in the source code
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeIdentifier {
    /// creates a new identifier node
    pub fn new(name: String, loc: VelosiTokenStream) -> Self {
        Self { name, loc }
    }
}

/// Implementation of the [Display] trait for [VelosiParseTreeIdentifier]
impl Display for VelosiParseTreeIdentifier {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", self.name)
    }
}

/// Implementation of the [Debug] trait for [VelosiParseTreeIdentifier]
impl Debug for VelosiParseTreeIdentifier {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(self, f)
    }
}

/// Conversion of [String] to [VelosiParseTreeIdentifier]
impl From<String> for VelosiParseTreeIdentifier {
    fn from(name: String) -> Self {
        Self::new(name, VelosiTokenStream::default())
    }
}

/// Conversion of &[str] to [VelosiParseTreeIdentifier]
impl From<&str> for VelosiParseTreeIdentifier {
    fn from(name: &str) -> Self {
        Self::new(name.to_string(), VelosiTokenStream::default())
    }
}
