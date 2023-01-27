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

//! # VelosiParser -- Parse Tree Map
//!
//! This module defines the StaticMap of a Unit
//!

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

// use crate functionality
use crate::parsetree::{
    VelosiParseTreeExpr, VelosiParseTreeFnCallExpr, VelosiParseTreeIdentifier,
    VelosiParseTreeRangeExpr,
};
use crate::VelosiTokenStream;

/// Represents possible nodes in the unit definitions
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiParseTreeMap {
    ListComp(Box<VelosiParseTreeMapListComp>),
    Explicit(Box<VelosiParseTreeMapExplicit>),
}

impl VelosiParseTreeMap {
    /// Returns the position of the node in the source code
    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiParseTreeMap::ListComp(node) => &node.loc,
            VelosiParseTreeMap::Explicit(node) => &node.loc,
        }
    }
}

impl Display for VelosiParseTreeMap {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiParseTreeMap::ListComp(map) => Display::fmt(map, f),
            VelosiParseTreeMap::Explicit(map) => Display::fmt(map, f),
        }
    }
}

/// Represents possible nodes in the unit definitions
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeMapExplicit {
    pub entries: Vec<VelosiParseTreeMapElement>,
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeMapExplicit {
    pub fn new(entries: Vec<VelosiParseTreeMapElement>, loc: VelosiTokenStream) -> Self {
        Self { entries, loc }
    }
}

impl Display for VelosiParseTreeMapExplicit {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "[")?;
        for (i, e) in self.entries.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{e}")?;
        }

        write!(f, "]")
    }
}

/// Represents possible nodes in the unit definitions
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeMapListComp {
    pub elm: VelosiParseTreeMapElement,
    pub var: VelosiParseTreeIdentifier,
    pub range: VelosiParseTreeRangeExpr,
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeMapListComp {
    pub fn new(
        elm: VelosiParseTreeMapElement,
        var: VelosiParseTreeIdentifier,
        range: VelosiParseTreeRangeExpr,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            elm,
            var,
            range,
            loc,
        }
    }
}

impl Display for VelosiParseTreeMapListComp {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "[{} for {} in {}]", self.elm, self.var, self.range)
    }
}

/// Represents possible nodes in the unit definitions
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeMapElement {
    pub src: Option<VelosiParseTreeRangeExpr>,
    pub dst: VelosiParseTreeFnCallExpr,
    pub offset: Option<VelosiParseTreeExpr>,
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeMapElement {
    pub fn new(
        src: Option<VelosiParseTreeRangeExpr>,
        dst: VelosiParseTreeFnCallExpr,
        offset: Option<VelosiParseTreeExpr>,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            src,
            dst,
            offset,
            loc,
        }
    }
}

impl Display for VelosiParseTreeMapElement {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if let Some(src) = &self.src {
            write!(f, "{src} => ")?;
        }
        write!(f, "{}", self.dst)?;
        if let Some(offset) = &self.offset {
            write!(f, " @ {offset}")?;
        }
        Ok(())
    }
}
