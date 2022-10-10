// VelosiParser -- a parser for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2021, 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiParser -- Parse Tree
//!
//! This module defines the parse tree for the Velosiraptor language.

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

// use crate functionality
use super::{VelosiParseTreeExpr, VelosiParseTreeType};
use crate::VelosiTokenStream;

/// A constant definition within the root or unit context
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeConstDef {
    /// the name of the constant
    pub name: String,
    /// the type of the constant
    pub ctype: VelosiParseTreeType,
    /// expression representing the value of the constnat
    pub value: VelosiParseTreeExpr,
    /// the location of the import clause
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeConstDef {
    pub fn new(
        name: String,
        ctype: VelosiParseTreeType,
        value: VelosiParseTreeExpr,
        loc: VelosiTokenStream,
    ) -> Self {
        VelosiParseTreeConstDef {
            name,
            ctype,
            value,
            loc,
        }
    }
}

/// Implementation of the [Display] trait for the [VelosiParseTreeConstDef] struct
impl Display for VelosiParseTreeConstDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "const {} : {} = {};", self.name, self.ctype, self.value)
    }
}

/// A parameter definition within the methods, unit, or quantifier context
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeParam {
    /// the name of the parameter
    pub name: String,
    /// the type of the param
    pub ptype: VelosiParseTreeType,
    /// the location of the import clause
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeParam {
    pub fn new(name: String, ptype: VelosiParseTreeType, loc: VelosiTokenStream) -> Self {
        VelosiParseTreeParam { name, ptype, loc }
    }
}

/// Implementation of the [Display] trait for the [VelosiParseTreeParam] struct
impl Display for VelosiParseTreeParam {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}: {}", self.name, self.ptype)
    }
}
