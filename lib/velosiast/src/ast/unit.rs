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

//! # VelosiAst -- Unit Definitions
//!
//! This module defines the Constant AST nodes of the langauge

use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use velosiparser::{
    VelosiParseTreeUnit, VelosiParseTreeUnitDef, VelosiParseTreeUnitNode, VelosiTokenStream,
};

use crate::ast::{
    types::{VelosiAstType, VelosiAstTypeInfo},
    VelosiAstConst, VelosiAstMethod, VelosiAstNode, VelosiAstParam,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstErrDoubleDef, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

use super::{VelosiAstIdentifier, VelosiAstState};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstUnitSegment {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstUnitSegment {
    pub fn ident_as_rc_string(&self) -> Rc<String> {
        self.ident.name.clone()
    }

    pub fn ident_as_str(&self) -> &str {
        self.ident.name.as_str()
    }

    pub fn ident_to_string(&self) -> String {
        self.ident.name.to_string()
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeUnitDef,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstUnit, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // create a new context in the symbol table
        st.create_context("unit".to_string());

        // convert all the unit parameters
        let mut params = Vec::new();
        for p in pt.params.into_iter() {
            let param = Rc::new(ast_result_unwrap!(
                VelosiAstParam::from_parse_tree(p, false, st),
                issues
            ));

            // here we want to check if the parameter are also defined on the unit level
            // and whether the types match precisely

            // add the param to the symbol table, if it doesn't exist already
            if let Err(e) = st.insert(param.clone().into()) {
                issues.push(e);
            }
            params.push(param);
        }

        let _derived = if let Some(d) = pt.derived {
            let d = VelosiAstIdentifier::from(d);
            utils::check_type_exists(&mut issues, st, &d);
            Some(d)
        } else {
            None
        };

        let mut methods_map = HashMap::new();
        let mut methods = Vec::new();
        let mut consts_map = HashMap::new();
        let mut consts = Vec::new();
        let mut inbitwidth = None;
        let mut outbitwidth = None;
        let mut state: Option<Rc<VelosiAstState>> = None;
        for node in pt.nodes.into_iter() {
            match node {
                VelosiParseTreeUnitNode::Const(c) => {
                    let c = Rc::new(ast_result_unwrap!(
                        VelosiAstConst::from_parse_tree(c, st),
                        issues
                    ));
                    if let Err(e) = st.insert(c.clone().into()) {
                        issues.push(e);
                    } else {
                        consts.push(c.clone());
                        consts_map.insert(c.ident_to_string(), c);
                    }
                }
                VelosiParseTreeUnitNode::InBitWidth(w, loc) => {
                    utils::check_addressing_width(&mut issues, w, loc);
                    inbitwidth = Some(w);
                }
                VelosiParseTreeUnitNode::OutBitWidth(w, loc) => {
                    utils::check_addressing_width(&mut issues, w, loc);
                    outbitwidth = Some(w);
                }
                VelosiParseTreeUnitNode::Flags(_flags) => (),
                VelosiParseTreeUnitNode::State(pst) => {
                    let s = Rc::new(ast_result_unwrap!(
                        VelosiAstState::from_parse_tree(pst, st),
                        issues
                    ));
                    if let Some(st) = &state {
                        let err = VelosiAstErrDoubleDef::new(
                            Rc::new(String::from("state")),
                            st.loc().clone(),
                            s.loc().clone(),
                        );
                        issues.push(err.into());
                    } else {
                        state = Some(s);
                    }
                }
                VelosiParseTreeUnitNode::Interface(_interface) => (),
                VelosiParseTreeUnitNode::Method(method) => {
                    let m = Rc::new(ast_result_unwrap!(
                        VelosiAstMethod::from_parse_tree(method, st),
                        issues
                    ));
                    if let Err(e) = st.insert(m.clone().into()) {
                        issues.push(e);
                    } else {
                        methods.push(m.clone());
                        methods_map.insert(m.ident_to_string(), m);
                    }
                }
                VelosiParseTreeUnitNode::Map(map) => {
                    let msg = "Ignored unit node: Map definitions are not supported in Segments.";
                    let hint = "Remove the map definition.";
                    let err = VelosiAstErrBuilder::warn(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(map.loc().clone())
                        .build();
                    issues.push(err);
                }
            }
        }

        let res = Self {
            ident: VelosiAstIdentifier::from(pt.name),
            loc: pt.loc,
        };

        // and restore the context again.
        st.drop_context();

        ast_result_return!(VelosiAstUnit::Segment(res), issues)
    }
}

/// Implementation of [Display] for [VelosiAstUnitSegment]
impl Display for VelosiAstUnitSegment {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "Segment ...")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstUnitStaticMap {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstUnitStaticMap {
    pub fn ident_as_rc_string(&self) -> Rc<String> {
        self.ident.name.clone()
    }

    pub fn ident_as_str(&self) -> &str {
        self.ident.name.as_str()
    }

    pub fn ident_to_string(&self) -> String {
        self.ident.name.to_string()
    }

    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        _pt: VelosiParseTreeUnitDef,
        _st: &mut SymbolTable,
    ) -> AstResult<VelosiAstUnit, VelosiAstIssues> {
        panic!("not implemented");
    }
}

/// Implementation of [Display] for [VelosiAstUnitStaticMap]
impl Display for VelosiAstUnitStaticMap {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "StaticMap ...")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiAstUnit {
    Segment(VelosiAstUnitSegment),
    StaticMap(VelosiAstUnitStaticMap),
}

impl VelosiAstUnit {
    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeUnit,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        use VelosiParseTreeUnit::*;
        match pt {
            Segment(pt) => VelosiAstUnitSegment::from_parse_tree(pt, st),
            StaticMap(pt) => VelosiAstUnitStaticMap::from_parse_tree(pt, st),
        }
    }

    pub fn ident_as_rc_string(&self) -> Rc<String> {
        match self {
            VelosiAstUnit::Segment(s) => s.ident_as_rc_string(),
            VelosiAstUnit::StaticMap(s) => s.ident_as_rc_string(),
        }
    }

    pub fn ident_as_str(&self) -> &str {
        match self {
            VelosiAstUnit::Segment(s) => s.ident_as_str(),
            VelosiAstUnit::StaticMap(s) => s.ident_as_str(),
        }
    }

    pub fn ident_to_string(&self) -> String {
        match self {
            VelosiAstUnit::Segment(s) => s.ident_to_string(),
            VelosiAstUnit::StaticMap(s) => s.ident_to_string(),
        }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiAstUnit::Segment(s) => &s.loc,
            VelosiAstUnit::StaticMap(s) => &s.loc,
        }
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstUnit>> for Symbol {
    fn from(unit: Rc<VelosiAstUnit>) -> Self {
        let ti = VelosiAstType::from(unit.clone());
        let name = unit.ident_as_rc_string();
        Symbol::new(name, ti, VelosiAstNode::Unit(unit))
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstUnit>> for VelosiAstType {
    fn from(unit: Rc<VelosiAstUnit>) -> Self {
        let name = unit.ident_as_rc_string();
        VelosiAstType::new(VelosiAstTypeInfo::TypeRef(name), unit.loc().clone())
    }
}

/// Implementation of [Display] for [VelosiAstUnit]
impl Display for VelosiAstUnit {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiAstUnit::Segment(s) => Display::fmt(s, f),
            VelosiAstUnit::StaticMap(s) => Display::fmt(s, f),
        }
    }
}
