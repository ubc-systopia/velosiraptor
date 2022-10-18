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

use velosiparser::{VelosiParseTreeUnit, VelosiParseTreeUnitDef, VelosiTokenStream};

use crate::ast::{
    types::{VelosiAstType, VelosiAstTypeInfo},
    VelosiAstNode, VelosiAstParam,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstUnitSegment {
    /// the name of the unit
    pub name: Rc<String>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstUnitSegment {
    pub fn from_parse_tree(
        pt: VelosiParseTreeUnitDef,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstUnit, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // create a new context in the symbol table
        st.create_context("unit".to_string());

        // convert all the unit parameters
        let mut params = HashMap::new();
        for p in pt.params.into_iter() {
            let param = Rc::new(ast_result_unwrap!(
                VelosiAstParam::from_parse_tree(p, false, st),
                issues
            ));

            // add the param to the symbol table, if it doesn't exist already
            if let Err(e) = st.insert(param.clone().into()) {
                issues.push(e);
            } else {
                params.insert(param.name.to_string(), param);
            }
        }

        let _derived = if let Some(d) = pt.derived {
            let d = Rc::new(d);
            let start = 5 + params.len() * 3 + params.len() - std::cmp::min(params.len(), 1);
            let range = start..start + 1;
            utils::check_type_exists(
                &mut issues,
                st,
                d.clone(),
                pt.pos.from_self_with_subrange(range),
            );
            Some(d)
        } else {
            None
        };

        let res = Self {
            name: Rc::new(pt.name),
            loc: pt.pos,
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
    pub name: Rc<String>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstUnitStaticMap {
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

    pub fn name(&self) -> &str {
        match self {
            VelosiAstUnit::Segment(s) => s.name.as_str(),
            VelosiAstUnit::StaticMap(s) => s.name.as_str(),
        }
    }

    pub fn name_cloned(&self) -> Rc<String> {
        match self {
            VelosiAstUnit::Segment(s) => s.name.clone(),
            VelosiAstUnit::StaticMap(s) => s.name.clone(),
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
        let name = unit.name_cloned();
        Symbol::new(name, ti, VelosiAstNode::Unit(unit))
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstUnit>> for VelosiAstType {
    fn from(c: Rc<VelosiAstUnit>) -> Self {
        let name = c.name_cloned();
        VelosiAstType::new(VelosiAstTypeInfo::TypeRef(name), c.loc().clone())
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
