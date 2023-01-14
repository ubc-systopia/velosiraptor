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
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstIdentifier {
    /// the identifier
    pub ident: Rc<String>,
    /// the path as a fully formatted string
    pub path: Rc<String>,
    /// the location of the identifier in the source pos
    pub loc: VelosiTokenStream,
}

/// the path separator
pub const IDENT_PATH_SEP: &str = ".";

use core::str::Split;

impl VelosiAstIdentifier {
    /// creates a new identifier token
    fn new(prefix: &str, name: String, loc: VelosiTokenStream) -> Self {
        let ident = Rc::new(name.clone());
        let path = if prefix.is_empty() {
            ident.clone()
        } else {
            let path = format!("{}{}{}", prefix, IDENT_PATH_SEP, name);
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
    pub consts: Vec<Rc<VelosiAstConst>>,
    pub consts_map: HashMap<String, Rc<VelosiAstConst>>,
    // pub abstract_map : HashMap<>,
    pub segments_map: HashMap<String, Rc<VelosiAstUnitSegment>>,
    pub staticmap_map: HashMap<String, Rc<VelosiAstUnitStaticMap>>,
    pub enum_map: HashMap<String, Rc<VelosiAstUnitEnum>>,
    pub context: String,
}

impl VelosiAstRoot {
    pub fn new(context: String) -> Self {
        Self {
            consts: Vec::new(),
            consts_map: HashMap::new(),
            segments_map: HashMap::new(),
            staticmap_map: HashMap::new(),
            enum_map: HashMap::new(),
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
        match u {
            VelosiAstUnit::Segment(s) => {
                self.segments_map.insert(s.ident_to_string(), s.clone());
            }
            VelosiAstUnit::StaticMap(s) => {
                self.staticmap_map.insert(s.ident_to_string(), s.clone());
            }
            VelosiAstUnit::Enum(f) => {
                self.enum_map.insert(f.ident_to_string(), f.clone());
            }
        }
    }

    pub fn unit_map(&self) -> HashMap<Rc<String>, VelosiAstUnit> {
        let mut units = HashMap::new();
        for u in self.segments_map.values() {
            if u.is_abstract {
                continue;
            }
            units.insert(u.ident().clone(), VelosiAstUnit::Segment(u.clone()));
        }
        for u in self.staticmap_map.values() {
            units.insert(u.ident().clone(), VelosiAstUnit::StaticMap(u.clone()));
        }
        for u in self.enum_map.values() {
            units.insert(u.ident().clone(), VelosiAstUnit::Enum(u.clone()));
        }
        units
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
                        root.add_const_rc(c);
                    }
                }
                VelosiParseTreeContextNode::Unit(u) => {
                    let c = ast_result_unwrap!(VelosiAstUnit::from_parse_tree(u, &mut st), issues);
                    if let Err(e) = st.insert(c.clone().into()) {
                        issues.push(*e);
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

    pub fn consts(&self) -> &[Rc<VelosiAstConst>] {
        self.consts.as_slice()
    }

    pub fn put_segment_unit(&mut self, unit: VelosiAstUnitSegment) {
        self.segments_map
            .insert(unit.ident_to_string(), Rc::new(unit));
    }

    pub fn take_segment_unit(&mut self) -> Option<VelosiAstUnitSegment> {
        if let Some((k, v)) = self.segments_map.drain().next() {
            if Rc::weak_count(&v) > 1 || Rc::strong_count(&v) > 1 {
                panic!("Segment unit {} is still in use!", k);
            }
            Some(Rc::try_unwrap(v).unwrap())
        } else {
            None
        }
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

        writeln!(f, "\nSegment Units:")?;

        for u in self.segments_map.values() {
            writeln!(f)?;
            Display::fmt(u, f)?;
            writeln!(f)?;
        }

        if self.segments_map.is_empty() {
            writeln!(f, "  <none>")?;
        }

        writeln!(f, "\nStaticMap Units:")?;

        for u in self.staticmap_map.values() {
            writeln!(f)?;
            Display::fmt(u, f)?;
            writeln!(f)?;
        }

        if self.segments_map.is_empty() {
            writeln!(f, "  <none>")?;
        }
        writeln!(
            f,
            "--------------------------------------------------------"
        )
    }
}
