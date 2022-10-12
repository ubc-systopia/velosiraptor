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
use crate::VelosiTokenStream;

pub mod constparams;
pub mod expr;
pub mod field;
pub mod interface;
pub mod state;
pub mod types;
pub mod unit;

pub use constparams::{VelosiParseTreeConstDef, VelosiParseTreeParam};
pub use expr::VelosiParseTreeExpr;
pub use field::{VelosiParseTreeField, VelosiParseTreeFieldSlice};
pub use interface::{
    VelosiParseTreeInterface, VelosiParseTreeInterfaceAction, VelosiParseTreeInterfaceActions,
    VelosiParseTreeInterfaceDef, VelosiParseTreeInterfaceField, VelosiParseTreeInterfaceFieldNode,
};
pub use state::{VelosiParseTreeState, VelosiParseTreeStateDef, VelosiParseTreeStateField};
pub use types::{VelosiParseTreeType, VelosiParseTreeTypeInfo};
pub use unit::{
    VelosiParseTreeFlag, VelosiParseTreeFlags, VelosiParseTreeMethod, VelosiParseTreeUnit,
    VelosiParseTreeUnitDef, VelosiParseTreeUnitNode,
};

/// Import clause in the root context
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
    Unit(VelosiParseTreeUnit),
}

/// Implement [Display] for [VelosiParseTree]
impl Display for VelosiParseTreeContextNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use VelosiParseTreeContextNode::*;
        match self {
            Const(c) => Display::fmt(&c, f),
            Import(i) => Display::fmt(&i, f),
            Unit(u) => Display::fmt(&u, f),
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
