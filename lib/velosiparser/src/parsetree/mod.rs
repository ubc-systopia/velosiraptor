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

//! # VelisoParser -- Parse Tree
//!
//! This module defines the parse tree for the Velosiraptor language.

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

//
use crate::VelosiTokenStream;

pub mod expr;

use crate::parsetree::expr::VelosiParseTreeExpr;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiParseTreeTypeInfo {
    Integer,
    Bool,
    GenAddr,
    VirtAddr,
    PhysAddr,
    Size,
    Flags,
    TypeRef(String),
}

impl Display for VelosiParseTreeTypeInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use VelosiParseTreeTypeInfo::*;
        match self {
            Integer => write!(f, "int"),
            Bool => write!(f, "bool"),
            GenAddr => write!(f, "addr"),
            VirtAddr => write!(f, "vaddr"),
            PhysAddr => write!(f, "paddr"),
            Size => write!(f, "size"),
            Flags => write!(f, "flags"),
            TypeRef(name) => write!(f, "{}", name),
        }
    }
}

/// Parameter Definitions
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeType {
    /// the type information
    pub typeinfo: VelosiParseTreeTypeInfo,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeType {
    pub fn new(typeinfo: VelosiParseTreeTypeInfo, loc: VelosiTokenStream) -> Self {
        VelosiParseTreeType { typeinfo, loc }
    }
}

impl Display for VelosiParseTreeType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Display::fmt(&self.typeinfo, f)
    }
}

/// Parameter Definitions
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

impl Display for VelosiParseTreeParam {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}: {}", self.name, self.ptype)
    }
}

/// Constant Definitions
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

impl Display for VelosiParseTreeConstDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "const {} : {} = {};", self.name, self.ctype, self.value)
    }
}

/// Import Clause
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiParseTreeImport {
    /// name of the imported module
    pub name: String,
    /// the location of the import clause
    pub loc: VelosiTokenStream,
}

impl Display for VelosiParseTreeImport {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "import {};", self.name)
    }
}

/// Represents parse tree nodes
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiParseTreeContextNode {
    Const(VelosiParseTreeConstDef),
    Import(VelosiParseTreeImport),
    Unit,
}

/// Implement [Display] for [VelosiParseTree]
impl Display for VelosiParseTreeContextNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use VelosiParseTreeContextNode::*;
        match self {
            Const(c) => Display::fmt(&c, f),
            Import(i) => Display::fmt(&i, f),
            Unit => write!(f, "unit"),
        }
    }
}

/// Represents the parse tree root for the velosiraptor language
pub struct VelosiParseTree {
    /// List of nodes in the current parse tree context
    nodes: Vec<VelosiParseTreeContextNode>,
    /// The current node context
    context: String,
}

impl VelosiParseTree {
    pub fn new(context: String, nodes: Vec<VelosiParseTreeContextNode>) -> Self {
        Self { nodes, context }
    }
}

/// Implement [Display] for [VelosiParseTree]
impl Display for VelosiParseTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "VelosiParseTree({})", self.context)?;
        writeln!(f, "---------------------------------------------")?;
        for n in &self.nodes {
            writeln!(f, "{}\n", n)?;
        }
        Ok(())
    }
}
