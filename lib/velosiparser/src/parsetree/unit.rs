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

//! # VelosiParser -- Parse Tree Type Node
//!
//! Parse tree nodes for type information

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

// use crate functionality
use super::{VelosiParseTreeConstDef, VelosiParseTreeParam};
use crate::VelosiTokenStream;

/// Represents possible nodes in the unit definitions
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiParseTreeUnitNode {
    Const(VelosiParseTreeConstDef),
    InBitWidth(u64, VelosiTokenStream),
    OutBitWidth(u64, VelosiTokenStream),
    Flags,
    State,
    Interface,
    Method,
    Map,
}

/// Implement [Display] for [VelosiParseTreeUnitNode]
impl Display for VelosiParseTreeUnitNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "TODO: implement display for VelosiParseTreeUnitNode")
    }
}

/// Represents a unit definition
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeUnitDef {
    /// the name of the unit (identifier)
    pub name: String,
    /// the unit parameters
    pub params: Vec<VelosiParseTreeParam>,
    /// the name of the derrived unit
    pub derived: Option<String>,
    /// the nodes defined in the parse tree
    pub nodes: Vec<VelosiParseTreeUnitNode>,
    /// the position in the source tree where this unit is defined
    pub pos: VelosiTokenStream,
}

impl VelosiParseTreeUnitDef {
    pub fn new(
        name: String,
        params: Vec<VelosiParseTreeParam>,
        derived: Option<String>,
        nodes: Vec<VelosiParseTreeUnitNode>,
        pos: VelosiTokenStream,
    ) -> Self {
        VelosiParseTreeUnitDef {
            name,
            params,
            derived,
            nodes,
            pos,
        }
    }
}

/// Implement [Display] for [VelosiParseTreeUnitDef]
impl Display for VelosiParseTreeUnitDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.name)?;
        if !self.params.is_empty() {
            write!(f, "(")?;
            for param in self.params.iter() {
                write!(f, "{}, ", param)?;
            }
            write!(f, ")")?;
        }

        if let Some(derived) = &self.derived {
            write!(f, " : {}", derived)?;
        }

        writeln!(f, " {{")?;
        for n in self.nodes.iter() {
            writeln!(f, "{}", n)?;
        }

        writeln!(f, "}}")
    }
}

/// Represent a unit
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiParseTreeUnit {
    Segment(VelosiParseTreeUnitDef),
    StaticMap(VelosiParseTreeUnitDef),
}

/// Implement [Display] for [VelosiParseTreeUnit]
impl Display for VelosiParseTreeUnit {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiParseTreeUnit::Segment(unit) => {
                write!(f, "segment ")?;
                Display::fmt(&unit, f)
            }
            VelosiParseTreeUnit::StaticMap(unit) => {
                write!(f, "staticmap ")?;
                Display::fmt(&unit, f)
            }
        }
    }
}
