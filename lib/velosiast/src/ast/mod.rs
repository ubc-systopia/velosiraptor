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
//! This module defines the AST of the language with its different AST nodes.

// modules
mod constdef;
mod expr;
mod fieldslice;
mod flags;
mod identifier;
mod interface;
mod map;
mod method;
mod operations;
mod param;
mod state;
mod types;
mod unit;

// public re-exports
pub use constdef::VelosiAstConst;
pub use expr::{
    VelosiAstBinOp, VelosiAstBinOpExpr, VelosiAstBoolLiteralExpr, VelosiAstExpr,
    VelosiAstFnCallExpr, VelosiAstIdentLiteralExpr, VelosiAstIfElseExpr, VelosiAstNumLiteralExpr,
    VelosiAstQuantifier, VelosiAstQuantifierExpr, VelosiAstRangeExpr, VelosiAstSliceExpr,
    VelosiAstUnOp, VelosiAstUnOpExpr,
};
pub use fieldslice::{VelosiAstField, VelosiAstFieldSlice};
pub use flags::VelosiAstFlags;
pub use identifier::VelosiAstIdentifier;
pub use interface::{
    VelosiAstInterface, VelosiAstInterfaceAction, VelosiAstInterfaceField,
    VelosiAstInterfaceMemoryField, VelosiAstInterfaceMmioField, VelosiAstInterfaceRegisterField,
};
pub use map::{
    VelosiAstStaticMap, VelosiAstStaticMapElement, VelosiAstStaticMapExplicit,
    VelosiAstStaticMapListComp,
};
pub use method::{VelosiAstMethod, VelosiAstMethodProperty};
pub use operations::{VelosiOpExpr, VelosiOperation};
pub use param::VelosiAstParam;
pub use state::{VelosiAstState, VelosiAstStateField};
pub use types::{VelosiAstType, VelosiAstTypeInfo, VelosiAstTypeProperty};
pub use unit::{
    VelosiAstUnit, VelosiAstUnitEnum, VelosiAstUnitOSSpec, VelosiAstUnitProperty,
    VelosiAstUnitSegment, VelosiAstUnitStaticMap,
};

// used standard library functionality

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

use std::rc::Rc;

// used third party cartes
use indexmap::{
    map::{Keys, Values, ValuesMut},
    IndexMap,
};

// used parse tree definitions
use velosiparser::parsetree::{VelosiParseTree, VelosiParseTreeContextNode};
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::VelosiAstIssues;
use crate::{ast_result_return, ast_result_unwrap, AstResult, SymbolTable};

use self::types::VelosiAstExternType;

////////////////////////////////////////////////////////////////////////////////////////////////////
// AST Node
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents a node in the AST.
///
/// This is a wrapper around the actual node that enables passing around AST nodes generically.
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
    ExternType(Rc<VelosiAstExternType>),
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
            ExternType(t) => &t.loc,
        }
    }
}

/// Defines the root note of the ast
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiAstRoot {
    pub consts: IndexMap<String, Rc<VelosiAstConst>>,
    pub units: IndexMap<String, VelosiAstUnit>,
    pub flags: Option<Rc<VelosiAstFlags>>,
    pub context: String,
}

impl VelosiAstRoot {
    pub fn new(context: String) -> Self {
        Self {
            consts: IndexMap::new(),
            units: IndexMap::new(),
            context,
            flags: None,
        }
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
                        issues.push(*e);
                    } else {
                        root.consts.insert(c.ident_to_string(), c);
                    }
                }
                VelosiParseTreeContextNode::Unit(u) => {
                    let c = ast_result_unwrap!(VelosiAstUnit::from_parse_tree(u, &mut st), issues);
                    if let Err(e) = st.insert(c.clone().into()) {
                        issues.push(*e);
                    } else {
                        root.units.insert(c.ident_to_string(), c);
                    }
                }
                VelosiParseTreeContextNode::Flags(f) => {
                    let c = Rc::new(ast_result_unwrap!(
                        VelosiAstFlags::from_parse_tree(f),
                        issues
                    ));
                    if let Err(e) = st.insert(c.clone().into()) {
                        debug_assert!(root.flags.is_some());
                        issues.push(*e);
                    } else {
                        root.flags = Some(c);
                    }
                }
                VelosiParseTreeContextNode::Type(_t) => {
                    todo!("implement me")
                }
                VelosiParseTreeContextNode::Import(_i) => {
                    unreachable!("Import nodes should have been removed!");
                }
            }
        }

        ast_result_return!(root, issues)
    }

    pub fn add_const(&mut self, c: VelosiAstConst) {
        self.consts.insert(c.ident_to_string(), Rc::new(c));
    }

    pub fn consts(&self) -> Values<String, Rc<VelosiAstConst>> {
        self.consts.values()
    }

    pub fn consts_mut(&mut self) -> ValuesMut<String, Rc<VelosiAstConst>> {
        self.consts.values_mut()
    }

    pub fn consts_idents(&self) -> Keys<String, Rc<VelosiAstConst>> {
        self.consts.keys()
    }

    pub fn get_const(&self, ident: &str) -> Option<&VelosiAstConst> {
        if let Some(c) = self.consts.get(ident) {
            Some(c.as_ref())
        } else {
            None
        }
    }

    pub fn get_const_mut(&mut self, ident: &str) -> Option<&mut VelosiAstConst> {
        if let Some(c) = self.consts.get_mut(ident) {
            if Rc::weak_count(c) > 1 || Rc::strong_count(c) > 1 {
                // warn!
            }
            Rc::get_mut(c)
        } else {
            None
        }
    }

    pub fn add_unit(&mut self, u: VelosiAstUnit) {
        self.units.insert(u.ident_to_string(), u);
    }

    pub fn units(&self) -> Values<String, VelosiAstUnit> {
        self.units.values()
    }

    pub fn units_mut(&mut self) -> ValuesMut<String, VelosiAstUnit> {
        self.units.values_mut()
    }

    pub fn units_idents(&self) -> Keys<String, VelosiAstUnit> {
        self.units.keys()
    }

    pub fn get_unit(&self, ident: &str) -> Option<&VelosiAstUnit> {
        self.units.get(ident)
    }

    pub fn get_unit_mut(&mut self, ident: &str) -> Option<&mut VelosiAstUnit> {
        self.units.get_mut(ident)
    }

    pub fn segments(&self) -> Vec<&VelosiAstUnitSegment> {
        self.units
            .iter()
            .filter_map(|(_k, v)| match v {
                VelosiAstUnit::Segment(e) => Some(e.as_ref()),
                _ => None,
            })
            .collect()
    }

    pub fn staticmaps(&self) -> Vec<&VelosiAstUnitStaticMap> {
        self.units
            .iter()
            .filter_map(|(_k, v)| match v {
                VelosiAstUnit::StaticMap(e) => Some(e.as_ref()),
                _ => None,
            })
            .collect()
    }

    pub fn enums(&self) -> Vec<&VelosiAstUnitEnum> {
        self.units
            .iter()
            .filter_map(|(_k, v)| match v {
                VelosiAstUnit::Enum(e) => Some(e.as_ref()),
                _ => None,
            })
            .collect()
    }

    pub fn osspec(&self) -> Option<&VelosiAstUnitOSSpec> {
        self.units
            .iter()
            .filter_map(|(_k, v)| match v {
                VelosiAstUnit::OSSpec(e) => Some(e.as_ref()),
                _ => None,
            })
            .next()
    }

    pub fn get_state_registers(&self) -> Vec<Rc<VelosiAstStateField>> {
        let mut regs = Vec::new();
        for u in self.units.values() {
            if let VelosiAstUnit::Segment(s) = u {
                regs.extend(s.get_state_registers())
            }
        }
        regs
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

        if !self.consts.is_empty() {
            writeln!(f)?;
            for c in self.consts.values() {
                Display::fmt(c, f)?;
                writeln!(f)?;
            }
        }

        if !self.units.is_empty() {
            writeln!(f)?;
            for u in self.units.values() {
                Display::fmt(u, f)?;
                writeln!(f, "\n")?;
            }
        }

        writeln!(
            f,
            "--------------------------------------------------------"
        )?;

        Ok(())
    }
}

/// Implementation of [Debug] for [VelosiAstRoot]
impl Debug for VelosiAstRoot {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        writeln!(f, "VelosiAst({})", self.context)?;
        writeln!(
            f,
            "--------------------------------------------------------"
        )?;
        writeln!(f, "\nConsts:")?;

        for c in self.consts.values() {
            writeln!(f)?;
            Display::fmt(c, f)?;
            writeln!(f)?;
        }

        if self.consts.is_empty() {
            writeln!(f, "  <none>")?;
        }

        writeln!(f, "\\b Units:")?;

        for u in self.units.values() {
            writeln!(f)?;
            Display::fmt(u, f)?;
            writeln!(f)?;
        }

        writeln!(
            f,
            "--------------------------------------------------------"
        )
    }
}

impl Default for VelosiAstRoot {
    fn default() -> Self {
        Self::new("default".to_string())
    }
}
