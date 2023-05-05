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
use core::str::Split;
use std::collections::hash_map::{Keys, Values, ValuesMut};
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use velosiparser::{
    VelosiParseTree, VelosiParseTreeContextNode, VelosiParseTreeIdentifier, VelosiTokenStream,
};

use crate::error::VelosiAstIssues;
use crate::{ast_result_return, ast_result_unwrap, AstResult, SymbolTable};

mod constdef;
mod expr;
mod field;
mod flags;
mod interface;
mod map;
mod method;
mod operations;
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
pub use field::VelosiAstField;
pub use flags::VelosiAstFlags;
pub use interface::{
    VelosiAstInterface, VelosiAstInterfaceAction, VelosiAstInterfaceField,
    VelosiAstInterfaceMemoryField, VelosiAstInterfaceMmioField, VelosiAstInterfaceRegisterField,
};
pub use map::{
    VelosiAstStaticMap, VelosiAstStaticMapElement, VelosiAstStaticMapExplicit,
    VelosiAstStaticMapListComp,
};
pub use method::VelosiAstMethod;
pub use operations::{VelosiOpExpr, VelosiOperation};
pub use param::VelosiAstParam;
pub use slice::VelosiAstFieldSlice;
pub use state::{VelosiAstState, VelosiAstStateField};
pub use types::{VelosiAstType, VelosiAstTypeInfo};
pub use unit::{VelosiAstUnit, VelosiAstUnitEnum, VelosiAstUnitSegment, VelosiAstUnitStaticMap};

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
#[derive(Eq, Clone, Debug)]
pub struct VelosiAstIdentifier {
    /// the identifier
    pub ident: Rc<String>,
    /// the path as a fully formatted string
    pub path: Rc<String>,
    /// the location of the identifier in the source pos
    pub loc: VelosiTokenStream,
}

impl PartialEq for VelosiAstIdentifier {
    fn eq(&self, other: &Self) -> bool {
        self.path == other.path && self.ident == other.ident
    }
}

/// Implementation of [Hash] for [VelosiAstIdentifier]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstIdentifier {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ident.hash(state);
        self.path.hash(state);
    }
}

/// the path separator
pub const IDENT_PATH_SEP: &str = ".";

impl VelosiAstIdentifier {
    /// creates a new identifier token
    fn new(prefix: &str, name: String, loc: VelosiTokenStream) -> Self {
        let ident = Rc::new(name.clone());
        let path = if prefix.is_empty() {
            ident.clone()
        } else {
            let path = format!("{prefix}{IDENT_PATH_SEP}{name}");
            Rc::new(path)
        };

        Self { ident, path, loc }
    }

    /// creates a new identifier from the give name
    pub fn with_name(name: String) -> Self {
        Self::new("", name, VelosiTokenStream::default())
    }

    pub fn extend(&mut self, other: Self) -> &mut Self {
        self.ident = Rc::new(format!("{}{}{}", self.ident, IDENT_PATH_SEP, other.ident));
        self.path = Rc::new(format!("{}{}{}", self.path, IDENT_PATH_SEP, other.path));
        self.loc.expand_until_end(&other.loc);
        self
    }

    pub fn extend_with_str(&mut self, slice: &str) -> &mut Self {
        self.ident = Rc::new(format!("{}{}{}", self.ident, IDENT_PATH_SEP, slice));
        self.path = Rc::new(format!("{}{}{}", self.path, IDENT_PATH_SEP, slice));
        self
    }

    /// convert the parse tree identifier to a ast identifier with the given prefix
    pub fn from_parse_tree_with_prefix(pt: VelosiParseTreeIdentifier, prefix: &str) -> Self {
        Self::new(prefix, pt.name, pt.loc)
    }

    /// obtains a reference to the identifier string
    pub fn ident(&self) -> &Rc<String> {
        &self.ident
    }

    /// return the identifier as a string slice
    pub fn as_str(&self) -> &str {
        self.ident.as_str()
    }

    /// obtains the path as a string
    pub fn path(&self) -> &Rc<String> {
        &self.path
    }

    pub fn path_split(&'_ self) -> Split<&'_ str> {
        self.path.split(IDENT_PATH_SEP)
    }
}

impl From<&str> for VelosiAstIdentifier {
    fn from(id: &str) -> Self {
        Self::with_name(id.to_string())
    }
}

impl From<VelosiParseTreeIdentifier> for VelosiAstIdentifier {
    fn from(id: VelosiParseTreeIdentifier) -> Self {
        Self::new("", id.name, id.loc)
    }
}

/// Implementation of the [Display] trait for [VelosiAstIdentifier]
impl Display for VelosiAstIdentifier {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", self.path)
    }
}

/// Defines the root note of the ast
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstRoot {
    pub consts: HashMap<String, Rc<VelosiAstConst>>,
    pub units: HashMap<String, VelosiAstUnit>,
    pub context: String,
}

impl VelosiAstRoot {
    pub fn new(context: String) -> Self {
        Self {
            consts: HashMap::new(),
            units: HashMap::new(),
            context,
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
