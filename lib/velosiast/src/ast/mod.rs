// VelosiAst -- a Ast for the Velosiraptor Language
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

//! # VelosiAst -- The Ast for the Velosiraptor Language
//!
//! This module defines the AST of the langauge

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use std::collections::HashMap;

use velosiparser::{
    VelosiParseTree, VelosiParseTreeContextNode, VelosiParseTreeIdentifier, VelosiTokenStream,
};

use crate::error::VelosiAstIssues;
use crate::{ast_result_return, ast_result_unwrap, AstResult, SymbolTable};

mod constdef;
mod expr;
mod flags;
mod interface;
mod map;
mod method;
mod param;
mod slice;
mod state;
mod types;
mod unit;

pub use constdef::VelosiAstConst;
pub use expr::{
    VelosiAstBinOp, VelosiAstBinOpExpr, VelosiAstBoolLiteralExpr, VelosiAstExpr,
    VelosiAstFnCallExpr, VelosiAstIdentLiteralExpr, VelosiAstIfElseExpr, VelosiAstNumLiteralExpr,
    VelosiAstQuantifier, VelosiAstQuantifierExpr, VelosiAstRangeExpr, VelosiAstSliceExpr,
    VelosiAstUnOp, VelosiAstUnOpExpr,
};
pub use flags::VelosiAstFlags;
pub use interface::{VelosiAstInterface, VelosiAstInterfaceAction, VelosiAstInterfaceField};
pub use map::{VelosiAstStaticMap, VelosiAstStaticMapElement};
pub use method::VelosiAstMethod;
pub use param::VelosiAstParam;
pub use slice::VelosiAstFieldSlice;
pub use state::{VelosiAstState, VelosiAstStateField};
pub use types::{VelosiAstType, VelosiAstTypeInfo};
pub use unit::{VelosiAstUnit, VelosiAstUnitSegment, VelosiAstUnitStaticMap};

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiAstNode {
    Unit(VelosiAstUnit),
    Const(Rc<VelosiAstConst>),
    Method(Rc<VelosiAstMethod>),
    Param(Rc<VelosiAstParam>),
    State(Rc<VelosiAstState>),
    StateField(Rc<VelosiAstStateField>),
    StateFieldSlice(Rc<VelosiAstFieldSlice>),
    Interface(Rc<VelosiAstInterface>),
    InterfaceField(Rc<VelosiAstInterfaceField>),
    InterfaceFieldSlice(Rc<VelosiAstFieldSlice>),
    Flags(Rc<VelosiAstFlags>),
    Flag(Rc<VelosiAstIdentifier>),
}

impl VelosiAstNode {
    pub fn loc(&self) -> &VelosiTokenStream {
        use VelosiAstNode::*;
        match self {
            Unit(u) => u.loc(),
            Const(c) => &c.loc,
            Method(m) => &m.loc,
            Param(p) => &p.loc,
            State(s) => s.loc(),
            StateField(sf) => sf.loc(),
            StateFieldSlice(sfs) => &sfs.loc,
            Interface(i) => i.loc(),
            InterfaceField(i) => i.loc(),
            InterfaceFieldSlice(i) => &i.loc,
            Flags(f) => &f.loc,
            Flag(f) => &f.loc,
        }
    }
}

/// represents an identifier token
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstIdentifier {
    pub name: Rc<String>,
    pub loc: VelosiTokenStream,
}

impl VelosiAstIdentifier {
    /// creates a new identifier token
    pub fn new(name: String, loc: VelosiTokenStream) -> Self {
        Self {
            name: Rc::new(name),
            loc,
        }
    }

    pub fn with_name(name: String) -> Self {
        Self::new(name, VelosiTokenStream::default())
    }

    pub fn from_parse_tree_with_prefix(pt: VelosiParseTreeIdentifier, prefix: &str) -> Self {
        let s = format!("{}.{}", prefix, pt.name);
        Self::new(s, pt.loc)
    }

    pub fn as_str(&self) -> &str {
        self.name.as_str()
    }
}

impl From<&str> for VelosiAstIdentifier {
    fn from(id: &str) -> Self {
        Self::new(id.to_string(), VelosiTokenStream::default())
    }
}

impl From<VelosiParseTreeIdentifier> for VelosiAstIdentifier {
    fn from(id: VelosiParseTreeIdentifier) -> Self {
        Self::new(id.name, id.loc)
    }
}

/// Implementation of the [Display] trait for [VelosiAstIdentifier]
impl Display for VelosiAstIdentifier {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", self.name)
    }
}

/// Defines the root note of the ast
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstRoot {
    pub consts: Vec<Rc<VelosiAstConst>>,
    pub consts_map: HashMap<String, Rc<VelosiAstConst>>,
    pub units: Vec<VelosiAstUnit>,
    pub units_map: HashMap<String, VelosiAstUnit>,
    pub context: String,
}

impl VelosiAstRoot {
    pub fn new(context: String) -> Self {
        Self {
            consts: Vec::new(),
            consts_map: HashMap::new(),
            units: Vec::new(),
            units_map: HashMap::new(),
            context,
        }
    }

    pub fn add_const(&mut self, c: VelosiAstConst) {
        let c = Rc::new(c);
        self.add_const_rc(c)
    }

    fn add_const_rc(&mut self, c: Rc<VelosiAstConst>) {
        self.consts_map.insert(c.ident_to_string(), c.clone());
        self.consts.push(c);
    }

    pub fn add_unit(&mut self, u: VelosiAstUnit) {
        self.units_map.insert(u.ident_to_string(), u.clone());
        self.units.push(u);
    }

    pub fn from_parse_tree(pt: VelosiParseTree) -> AstResult<VelosiAstRoot, VelosiAstIssues> {
        let mut root = Self::new(pt.context.unwrap_or_else(|| "$buf".to_string()));

        // create the symbol table

        let mut st = SymbolTable::new();
        let mut issues = VelosiAstIssues::new();

        // loop throug the nodes and try to conver them into the ast nodes.
        // if we hit a non-recoverable error, we simply abort and
        for n in pt.nodes {
            match n {
                VelosiParseTreeContextNode::Const(c) => {
                    let c = Rc::new(ast_result_unwrap!(
                        VelosiAstConst::from_parse_tree(c, &mut st),
                        issues
                    ));
                    if let Err(e) = st.insert(c.clone().into()) {
                        issues.push(e);
                    } else {
                        root.add_const_rc(c);
                    }
                }
                VelosiParseTreeContextNode::Unit(u) => {
                    let c = ast_result_unwrap!(VelosiAstUnit::from_parse_tree(u, &mut st), issues);
                    if let Err(e) = st.insert(c.clone().into()) {
                        issues.push(e);
                    } else {
                        root.add_unit(c);
                    }
                }
                VelosiParseTreeContextNode::Import(_i) => {
                    unreachable!("Import nodes should have been removed!");
                }
            }
        }

        ast_result_return!(root, issues)
    }

    pub fn units(&self) -> &[VelosiAstUnit] {
        self.units.as_slice()
    }
}

/// Implementation of [Display] for [VelosiAstRoot]
impl Display for VelosiAstRoot {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        writeln!(f, "VelosiAst({})", self.context)?;
        writeln!(
            f,
            "--------------------------------------------------------"
        )?;
        writeln!(f, "\nConsts:")?;

        for c in self.consts.iter() {
            writeln!(f)?;
            Display::fmt(c, f)?;
            writeln!(f)?;
        }

        if self.consts.is_empty() {
            writeln!(f, "  <none>")?;
        }

        writeln!(f, "\nUnits:")?;

        for u in self.units.iter() {
            writeln!(f)?;
            Display::fmt(u, f)?;
            writeln!(f)?;
        }

        if self.units.is_empty() {
            writeln!(f, "  <none>")?;
        }
        writeln!(
            f,
            "--------------------------------------------------------"
        )
    }
}
