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

//! # VelosiParser -- Parse Tree Nodes for State
//!
//! Parse tree nodes for state information

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

// used crate functionality
use crate::parsetree::{
    VelosiParseTreeFieldSlice, VelosiParseTreeIdentifier, VelosiParseTreeParam,
};
use crate::VelosiTokenStream;

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeStateFieldMemory {
    pub name: VelosiParseTreeIdentifier,
    pub base: VelosiParseTreeIdentifier,
    pub offset: u64,
    pub size: u64,
    pub layout: Vec<VelosiParseTreeFieldSlice>,
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeStateFieldMemory {
    pub fn new(
        name: VelosiParseTreeIdentifier,
        base: VelosiParseTreeIdentifier,
        offset: u64,
        size: u64,
        layout: Vec<VelosiParseTreeFieldSlice>,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            name,
            base,
            offset,
            size,
            layout,
            loc,
        }
    }
}

impl Display for VelosiParseTreeStateFieldMemory {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "mem {} [", self.name)?;
        write!(f, "{}, {}, ", self.base, self.offset)?;
        write!(f, "{}", self.size)?;
        writeln!(f, "] {{")?;
        for slice in &self.layout {
            write!(f, "      ")?;
            Display::fmt(slice, f)?;
            writeln!(f, ",")?;
        }
        write!(f, "    }}")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeStateFieldRegister {
    pub name: VelosiParseTreeIdentifier,
    pub size: u64,
    pub layout: Vec<VelosiParseTreeFieldSlice>,
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeStateFieldRegister {
    pub fn new(
        name: VelosiParseTreeIdentifier,
        size: u64,
        layout: Vec<VelosiParseTreeFieldSlice>,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            name,
            size,
            layout,
            loc,
        }
    }
}

impl Display for VelosiParseTreeStateFieldRegister {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "mem {} [", self.name)?;
        write!(f, "{}", self.size)?;
        writeln!(f, "] {{")?;
        for slice in &self.layout {
            write!(f, "      ")?;
            Display::fmt(slice, f)?;
            writeln!(f, ",")?;
        }
        write!(f, "    }}")
    }
}

/// Represents a component of the state, either a register or a memory location
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiParseTreeStateField {
    Memory(VelosiParseTreeStateFieldMemory),
    Register(VelosiParseTreeStateFieldRegister),
}

impl Display for VelosiParseTreeStateField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use VelosiParseTreeStateField::*;
        match self {
            Memory(field) => Display::fmt(field, f),
            Register(field) => Display::fmt(field, f),
        }
    }
}

/// Represents the parsed state description
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeStateDef {
    /// parameters of the state
    pub params: Vec<VelosiParseTreeParam>,
    /// the fields defined in teh state
    pub fields: Vec<VelosiParseTreeStateField>,
    /// the position in the source file
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeStateDef {
    /// Create a new state definition
    pub fn new(
        params: Vec<VelosiParseTreeParam>,
        fields: Vec<VelosiParseTreeStateField>,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            params,
            fields,
            loc,
        }
    }
}

impl Display for VelosiParseTreeStateDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if !self.params.is_empty() {
            write!(f, "StateDef(")?;
            for param in &self.params {
                Display::fmt(param, f)?;
            }
            write!(f, ")")?;
        }
        writeln!(f, " {{")?;
        for field in &self.fields {
            Display::fmt(field, f)?;
            writeln!(f, ",")?;
        }
        writeln!(f, "  }};")
    }
}

/// Represents the state definition
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiParseTreeState {
    StateDef(VelosiParseTreeStateDef),
    None(VelosiTokenStream),
}

impl VelosiParseTreeState {
    /// obtains the source position of the state definition
    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiParseTreeState::StateDef(def) => &def.loc,
            VelosiParseTreeState::None(loc) => loc,
        }
    }
}

impl Display for VelosiParseTreeState {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiParseTreeState::StateDef(s) => Display::fmt(&s, f),
            VelosiParseTreeState::None(_) => {
                writeln!(f, "None;")
            }
        }
    }
}
