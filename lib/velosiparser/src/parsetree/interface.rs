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

//! # VelosiParser -- Parse Tree Interface
//!
//! This module defines the interface nodes of the VelosiRaptor parse tree.

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

// used crate functionality
use super::{VelosiParseTreeExpr, VelosiParseTreeFieldSlice, VelosiParseTreeParam};
use crate::VelosiTokenStream;

/// Represents a state field
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeInterfaceAction {
    pub src: VelosiParseTreeExpr,
    pub dst: VelosiParseTreeExpr,
    pub pos: VelosiTokenStream,
}

impl VelosiParseTreeInterfaceAction {
    pub fn new(src: VelosiParseTreeExpr, dst: VelosiParseTreeExpr, pos: VelosiTokenStream) -> Self {
        Self { src, dst, pos }
    }
}

/// Represents a state field
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeInterfaceActions {
    pub actions: Vec<VelosiParseTreeInterfaceAction>,
    pub pos: VelosiTokenStream,
}

impl VelosiParseTreeInterfaceActions {
    pub fn new(actions: Vec<VelosiParseTreeInterfaceAction>, pos: VelosiTokenStream) -> Self {
        Self { actions, pos }
    }
}

impl Display for VelosiParseTreeInterfaceActions {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "action")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiParseTreeInterfaceFieldNode {
    Layout(Vec<VelosiParseTreeFieldSlice>),
    ReadActions(VelosiParseTreeInterfaceActions),
    WriteActions(VelosiParseTreeInterfaceActions),
    ReadWriteActions(VelosiParseTreeInterfaceActions),
}

/// Represents a state field
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeInterfaceField {
    pub name: String,
    pub offset: Option<(String, u64)>,
    pub size: u64,
    pub nodes: Vec<VelosiParseTreeInterfaceFieldNode>,
    pub pos: VelosiTokenStream,
}

impl VelosiParseTreeInterfaceField {
    pub fn new(
        name: String,
        offset: Option<(String, u64)>,
        size: u64,
        nodes: Vec<VelosiParseTreeInterfaceFieldNode>,
        pos: VelosiTokenStream,
    ) -> Self {
        Self {
            name,
            offset,
            size,
            nodes,
            pos,
        }
    }
}

impl Display for VelosiParseTreeInterfaceField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "interfac field")
        // write!(f, "{} [", self.name)?;
        // if let Some((name, num)) = &self.offset {
        //     write!(f, "{}, {},", name, num)?;
        // }
        // write!(f, "{}", self.size)?;
        // writeln!(f, "] {{")?;
        // for slice in &self.layout {
        //     Display::fmt(slice, f)?;
        //     writeln!(f, ",")?;
        // }
        // writeln!(f, "}}")
    }
}

/// Represents the parsed state description
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeInterfaceDef {
    /// parameters of the state
    pub params: Vec<VelosiParseTreeParam>,
    /// the fields defined in teh state
    pub fields: Vec<VelosiParseTreeInterfaceField>,
    /// the position in the source file
    pub pos: VelosiTokenStream,
}

impl VelosiParseTreeInterfaceDef {
    /// Create a new state definition
    pub fn new(
        params: Vec<VelosiParseTreeParam>,
        fields: Vec<VelosiParseTreeInterfaceField>,
        pos: VelosiTokenStream,
    ) -> Self {
        Self {
            params,
            fields,
            pos,
        }
    }
}

impl Display for VelosiParseTreeInterfaceDef {
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
pub enum VelosiParseTreeInterface {
    Memory(VelosiParseTreeInterfaceDef),
    MMIORegister(VelosiParseTreeInterfaceDef),
    CPURegister(VelosiParseTreeInterfaceDef),
    None(VelosiTokenStream),
}

impl Display for VelosiParseTreeInterface {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiParseTreeInterface::Memory(s) => {
                write!(f, "MemoryInterface")?;
                Display::fmt(&s, f)
            }
            VelosiParseTreeInterface::MMIORegister(s) => {
                write!(f, "MMIORegisterInterface")?;
                Display::fmt(&s, f)
            }
            VelosiParseTreeInterface::CPURegister(s) => {
                write!(f, "CPURegisterInterface")?;
                Display::fmt(&s, f)
            }
            VelosiParseTreeInterface::None(_) => {
                writeln!(f, "None;")
            }
        }
    }
}
