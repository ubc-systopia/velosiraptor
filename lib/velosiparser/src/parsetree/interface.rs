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
use super::{
    VelosiParseTreeExpr, VelosiParseTreeFieldSlice, VelosiParseTreeIdentifier, VelosiParseTreeParam,
};
use crate::VelosiTokenStream;

/// Represents a state field
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeInterfaceAction {
    pub src: VelosiParseTreeExpr,
    pub dst: VelosiParseTreeExpr,
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeInterfaceAction {
    pub fn new(src: VelosiParseTreeExpr, dst: VelosiParseTreeExpr, loc: VelosiTokenStream) -> Self {
        Self { src, dst, loc }
    }
}

impl Display for VelosiParseTreeInterfaceAction {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{} -> {};", self.src, self.dst)
    }
}

/// Implementation of [Debug] for [VelosiParseTreeInterfaceAction]
impl Debug for VelosiParseTreeInterfaceAction {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Represents a state field
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeInterfaceActions {
    pub actions: Vec<VelosiParseTreeInterfaceAction>,
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeInterfaceActions {
    pub fn new(actions: Vec<VelosiParseTreeInterfaceAction>, loc: VelosiTokenStream) -> Self {
        Self { actions, loc }
    }
}

impl Display for VelosiParseTreeInterfaceActions {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        for a in &self.actions {
            writeln!(f, "{a}")?;
        }
        Ok(())
    }
}

/// Implementation of [Debug] for [VelosiParseTreeInterfaceActions]
impl Debug for VelosiParseTreeInterfaceActions {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

#[derive(PartialEq, Eq, Clone)]
pub enum VelosiParseTreeInterfaceFieldNode {
    Layout(Vec<VelosiParseTreeFieldSlice>),
    ReadActions(VelosiParseTreeInterfaceActions),
    WriteActions(VelosiParseTreeInterfaceActions),
    // ReadWriteActions(VelosiParseTreeInterfaceActions),
}

impl Display for VelosiParseTreeInterfaceFieldNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiParseTreeInterfaceFieldNode::Layout(slices) => {
                writeln!(f, "Layout {{")?;
                for slice in slices {
                    writeln!(f, "  {slice},")?;
                }
                write!(f, "}}")?;
            }
            VelosiParseTreeInterfaceFieldNode::ReadActions(a) => {
                writeln!(f, "ReadActions {{")?;
                let formatted = format!("{a}");
                for l in formatted.lines() {
                    writeln!(f, "  {l}")?;
                }
                write!(f, "}}")?;
            }
            VelosiParseTreeInterfaceFieldNode::WriteActions(a) => {
                writeln!(f, "WriteActions {{")?;
                let formatted = format!("{a}");
                for l in formatted.lines() {
                    writeln!(f, "  {l}")?;
                }
                write!(f, "}}")?;
            }
        }
        Ok(())
    }
}

/// Implementation of [Debug] for [VelosiParseTreeInterfaceFieldNode]
impl Debug for VelosiParseTreeInterfaceFieldNode {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Represents a state field
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeInterfaceFieldMemory {
    pub name: VelosiParseTreeIdentifier,
    pub base: VelosiParseTreeIdentifier,
    pub offset: u64,
    pub size: u64,
    pub nodes: Vec<VelosiParseTreeInterfaceFieldNode>,
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeInterfaceFieldMemory {
    pub fn new(
        name: VelosiParseTreeIdentifier,
        base: VelosiParseTreeIdentifier,
        offset: u64,
        size: u64,
        nodes: Vec<VelosiParseTreeInterfaceFieldNode>,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            name,
            base,
            offset,
            size,
            nodes,
            loc,
        }
    }
}

impl Display for VelosiParseTreeInterfaceFieldMemory {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "mem {} [ ", self.name)?;
        write!(f, "{}, {}, ", self.base, self.offset)?;
        write!(f, "{} ]", self.size)?;
        if !self.nodes.is_empty() {
            writeln!(f, " {{")?;
            for node in &self.nodes {
                let formatted = format!("{node}");
                for (i, l) in formatted.lines().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "  {l}")?;
                }
                writeln!(f, ",")?;
            }
            write!(f, "}}")?;
        }
        Ok(())
    }
}

/// Implementation of [Debug] for [VelosiParseTreeInterfaceFieldMemory]
impl Debug for VelosiParseTreeInterfaceFieldMemory {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Represents a state field
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeInterfaceFieldMmio {
    pub name: VelosiParseTreeIdentifier,
    pub base: VelosiParseTreeIdentifier,
    pub offset: u64,
    pub size: u64,
    pub nodes: Vec<VelosiParseTreeInterfaceFieldNode>,
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeInterfaceFieldMmio {
    pub fn new(
        name: VelosiParseTreeIdentifier,
        base: VelosiParseTreeIdentifier,
        offset: u64,
        size: u64,
        nodes: Vec<VelosiParseTreeInterfaceFieldNode>,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            name,
            base,
            offset,
            size,
            nodes,
            loc,
        }
    }
}

impl Display for VelosiParseTreeInterfaceFieldMmio {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "mmio {} [ ", self.name)?;
        write!(f, "{}, {}, ", self.base, self.offset)?;
        write!(f, "{} ]", self.size)?;
        if !self.nodes.is_empty() {
            writeln!(f, " {{")?;
            for node in &self.nodes {
                let formatted = format!("{node}");
                for (i, l) in formatted.lines().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "  {l}")?;
                }
                writeln!(f, ",")?;
            }
            write!(f, "}}")?;
        }
        Ok(())
    }
}

/// Implementation of [Debug] for [VelosiParseTreeInterfaceFieldMmio]
impl Debug for VelosiParseTreeInterfaceFieldMmio {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Represents a state field
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeInterfaceFieldRegister {
    pub name: VelosiParseTreeIdentifier,
    pub size: u64,
    pub nodes: Vec<VelosiParseTreeInterfaceFieldNode>,
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeInterfaceFieldRegister {
    pub fn new(
        name: VelosiParseTreeIdentifier,
        size: u64,
        nodes: Vec<VelosiParseTreeInterfaceFieldNode>,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            name,
            size,
            nodes,
            loc,
        }
    }
}

impl Display for VelosiParseTreeInterfaceFieldRegister {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "reg {} [ ", self.name)?;
        write!(f, "{} ]", self.size)?;
        if !self.nodes.is_empty() {
            writeln!(f, " {{")?;
            for node in &self.nodes {
                let formatted = format!("{node}");
                for (i, l) in formatted.lines().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "  {l}")?;
                }
                writeln!(f, ",")?;
            }
            write!(f, "}}")?;
        }
        Ok(())
    }
}

/// Implementation of [Debug] for [VelosiParseTreeInterfaceFieldRegister]
impl Debug for VelosiParseTreeInterfaceFieldRegister {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Represents a component of the state, either a register or a memory location
#[derive(PartialEq, Eq, Clone)]
pub enum VelosiParseTreeInterfaceField {
    Memory(VelosiParseTreeInterfaceFieldMemory),
    Mmio(VelosiParseTreeInterfaceFieldMmio),
    Register(VelosiParseTreeInterfaceFieldRegister),
}

impl Display for VelosiParseTreeInterfaceField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use VelosiParseTreeInterfaceField::*;
        match self {
            Memory(field) => Display::fmt(field, f),
            Mmio(field) => Display::fmt(field, f),
            Register(field) => Display::fmt(field, f),
        }
    }
}

/// Implementation of [Debug] for [VelosiParseTreeInterfaceField]
impl Debug for VelosiParseTreeInterfaceField {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Represents the parsed state description
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeInterface {
    /// parameters of the state
    pub params: Vec<VelosiParseTreeParam>,
    /// the fields defined in teh state
    pub fields: Vec<VelosiParseTreeInterfaceField>,
    /// the position in the source file
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeInterface {
    /// Create a new state definition
    pub fn new(
        params: Vec<VelosiParseTreeParam>,
        fields: Vec<VelosiParseTreeInterfaceField>,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            params,
            fields,
            loc,
        }
    }

    /// obtains the source position of the state definition
    pub fn loc(&self) -> &VelosiTokenStream {
        &self.loc
    }
}

impl Display for VelosiParseTreeInterface {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "interface(")?;
        for (i, param) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            Display::fmt(param, f)?;
        }
        writeln!(f, ") {{")?;
        for field in &self.fields {
            let formatted = format!("{}", field);
            for (i, line) in formatted.lines().enumerate() {
                if i > 0 {
                    writeln!(f)?;
                }
                write!(f, "  {line}")?;
            }
            writeln!(f, ",")?;
        }
        write!(f, "}}")
    }
}

/// Implementation of [Debug] for [VelosiParseTreeInterface]
impl Debug for VelosiParseTreeInterface {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
