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

use crate::sourcepos::SourcePos;
use std::fmt;

/// Defines the state of a translation unit
///
/// The State defines how the translation unit will translate incoming addresses.
/// There are three fundamental state types:
///   - Memory: the state is *external* to the translation unit in some memory (e.g, RAM)
///   - Register: the state is *internal* to the translation unit
///   - None: there is no state associated with it.
#[derive(PartialEq, Clone)]
pub enum State {
    /// defines a memory state (external to the unit)
    MemoryState {
        /// a list of identifiers referring to memory regions
        bases: Vec<String>,
        /// defines a list of fields within the memory regions, defined by the bases
        fields: Vec<Field>,
        /// position where this state was defined
        pos: SourcePos,
    },
    /// defines a register state (internal to the unit)
    RegisterState {
        /// defines a list of fields that form the state
        fields: Vec<Field>,
        /// the position where the state is defined
        pos: SourcePos,
    },
    // TODO state that may be combined
    //CombinedState {  },
    /// No state associated with this translation unit
    None,
}

/// implementation of the [fmt::Display] trait for the [State]
impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::State::*;
        match self {
            MemoryState { bases, fields, pos } => {
                write!(f, "State(Memory) [")?;
                bases
                    .iter()
                    .fold(Ok(()), |result, b| result.and_then(|_| write!(f, "{} ", b)))?;
                writeln!(f, "] {{")?;

                fields.iter().fold(Ok(()), |result, field| {
                    result.and_then(|_| writeln!(f, "{}", field))
                })?;
                writeln!(f, "}}")
            }
            RegisterState { fields, pos } => {
                let s = String::new();
                writeln!(f, "State(Registers) {{")?;
                fields.iter().fold(Ok(()), |result, field| {
                    result.and_then(|_| writeln!(f, "{}", field))
                })?;
                writeln!(f, "}}")
            }
            None => writeln!(f, "State(None)"),
        }
    }
}

/// implementation of the [fmt::Debug] trait for the [State]
impl fmt::Debug for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::State::*;
        //let (line, column) = self.pos.input_pos();
        match self {
            MemoryState { bases, fields, pos } => {
                let (line, column) = pos.input_pos();
                write!(f, "{:03}:{:03} | State(Memory) [", line, column)?;
                bases
                    .iter()
                    .fold(Ok(()), |result, b| result.and_then(|_| write!(f, "{} ", b)))?;
                writeln!(f, "] {{")?;

                fields.iter().fold(Ok(()), |result, field| {
                    result.and_then(|_| writeln!(f, "{}", field))
                })?;
                writeln!(f, "}}")
            }
            RegisterState { fields, pos } => {
                let (line, column) = pos.input_pos();
                let s = String::new();
                writeln!(f, "{:03}:{:03} | State(Registers) {{", line, column)?;
                fields.iter().fold(Ok(()), |result, field| {
                    result.and_then(|_| writeln!(f, "{}", field))
                })?;
                writeln!(f, "}}")
            }
            None => writeln!(f, "State(None)"),
        }
    }
}

/// Defines an field in the state
///
/// A field may represent a 8, 16, 32, or 64 bit region in the state with a
/// specific bit layout.
#[derive(PartialEq, Clone)]
pub struct Field {
    /// the name of the field
    pub name: String,
    /// a reference to the state where the field is (base + offset)
    pub stateref: Option<(String, u64)>,
    /// the size of the field in bits
    pub length: u64,
    /// a vector of [BitSlice] representing the bitlayout
    pub layout: Vec<BitSlice>,
    /// the position where this field was defined
    pub pos: SourcePos,
}

/// Implementation of the [fmt::Display] trait for [Field]
impl fmt::Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.stateref {
            Some((s, o)) => writeln!(f, "{} [{}, {}, {}] {{", self.name, s, o, self.length)?,
            None => writeln!(f, "{} [{}] {{", self.name, self.length)?,
        };

        self.layout.iter().fold(Ok(()), |result, field| {
            result.and_then(|_| writeln!(f, "  {}", field))
        })?;
        writeln!(f, "}}")
    }
}

/// Implementation of the [fmt::Debug] trait for [Field]
impl fmt::Debug for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.pos.input_pos();
        write!(f, "{:03}:{:03} | ", line, column)?;
        match &self.stateref {
            Some((s, o)) => writeln!(f, "{} [{}, {}, {}] {{", self.name, s, o, self.length)?,
            None => writeln!(f, "{} [{}] {{", self.name, self.length)?,
        };

        self.layout.iter().fold(Ok(()), |result, field| {
            result.and_then(|_| writeln!(f, "  {:?}", field))
        })?;
        writeln!(f, "}}")
    }
}

/// Represents a bitslice of a [Field]
///
/// The field corresponds to the slice `[start..end]` of the [Field]
#[derive(PartialEq, Clone)]
pub struct BitSlice {
    /// the start bit
    pub start: u16,
    /// the end bit
    pub end: u16,
    /// the name of the slice
    pub name: String,
    /// where it was defined
    pub pos: SourcePos,
}

/// Implementation of the [fmt::Display] trait for [BitSlice]
impl fmt::Display for BitSlice {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[{:2}..{:2}]  {}", self.start, self.end, &self.name)
    }
}
/// Implementation of the [fmt::Debug] trait for [BitSlice]
impl fmt::Debug for BitSlice {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.pos.input_pos();
        write!(
            f,
            "{:03}:{:03} | [{:2}..{:2}]  {}",
            line, column, self.start, self.end, &self.name
        )
    }
}
