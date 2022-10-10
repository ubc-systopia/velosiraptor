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
use super::VelosiParseTreeParam;
use crate::VelosiTokenStream;

/// Represents the state definition
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeFieldSlice {
    pub start: u64,
    pub end: u64,
    pub name: String,
    pub pos: VelosiTokenStream,
}

impl VelosiParseTreeFieldSlice {
    pub fn new(start: u64, end: u64, name: String, pos: VelosiTokenStream) -> Self {
        Self {
            start,
            end,
            name,
            pos,
        }
    }
}

impl Display for VelosiParseTreeFieldSlice {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}..{} {}", self.start, self.end, self.name)
    }
}

/// Represents a state field
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeStateField {
    pub name: String,
    pub offset: Option<(String, u64)>,
    pub size: u64,
    pub layout: Vec<VelosiParseTreeFieldSlice>,
    pub pos: VelosiTokenStream,
}

impl VelosiParseTreeStateField {
    pub fn new(
        name: String,
        offset: Option<(String, u64)>,
        size: u64,
        layout: Vec<VelosiParseTreeFieldSlice>,
        pos: VelosiTokenStream,
    ) -> Self {
        Self {
            name,
            offset,
            size,
            layout,
            pos,
        }
    }
}

impl Display for VelosiParseTreeStateField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{} [", self.name)?;
        if let Some((name, num)) = &self.offset {
            write!(f, "{}, {},", name, num)?;
        }
        write!(f, "{}", self.size)?;
        writeln!(f, "] {{")?;
        for slice in &self.layout {
            Display::fmt(slice, f)?;
            writeln!(f, ",")?;
        }
        writeln!(f, "}}")
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
    pub pos: VelosiTokenStream,
}

impl VelosiParseTreeStateDef {
    /// Create a new state definition
    pub fn new(
        params: Vec<VelosiParseTreeParam>,
        fields: Vec<VelosiParseTreeStateField>,
        pos: VelosiTokenStream,
    ) -> Self {
        Self {
            params,
            fields,
            pos,
        }
    }
}

impl Display for VelosiParseTreeStateDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if !self.params.is_empty() {
            write!(f, "(")?;
            for param in &self.params {
                Display::fmt(param, f)?;
            }
            write!(f, ")")?;
        }
        writeln!(f, " {{")?;
        for field in &self.fields {
            Display::fmt(field, f)?;
        }
        writeln!(f, " }};")
    }
}

/// Represents the state definition
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiParseTreeState {
    Memory(VelosiParseTreeStateDef),
    Register(VelosiParseTreeStateDef),
    None(VelosiTokenStream),
}

impl Display for VelosiParseTreeState {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiParseTreeState::Memory(s) => {
                write!(f, "MemoryState")?;
                Display::fmt(&s, f)
            }
            VelosiParseTreeState::Register(s) => {
                write!(f, "RegisterState")?;
                Display::fmt(&s, f)
            }
            VelosiParseTreeState::None(_) => {
                writeln!(f, "None;")
            }
        }
    }
}
