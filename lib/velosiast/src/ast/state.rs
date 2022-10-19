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
    VelosiParseTreeState, VelosiParseTreeStateDef, VelosiParseTreeUnitNode, VelosiTokenStream,
};

use crate::ast::{
    types::{VelosiAstType, VelosiAstTypeInfo},
    VelosiAstConst, VelosiAstMethod, VelosiAstNode, VelosiAstParam,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstField {}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstMemoryState {
    /// the name of the unit
    pub name: Rc<String>,
    /// the parameters of the memory state
    pub params: Vec<Rc<VelosiAstParam>>,
    /// a map of the parameter states
    pub params_map: HashMap<String, Rc<VelosiAstParam>>,
    /// all the fields of this state
    pub fields: Vec<Rc<VelosiAstField>>,
    /// a map of strings to fields
    pub fields_map: HashMap<String, Rc<VelosiAstField>>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstMemoryState {
    pub fn from_parse_tree(
        pt: VelosiParseTreeStateDef,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstState, VelosiAstIssues> {
        // let mut issues = VelosiAstIssues::new();
        panic!("foobar");
        // ast_result_return!(VelosiAstState::MemoryState(res), issues)
    }
}

/// Implementation of [Display] for [VelosiAstMemoryState]
impl Display for VelosiAstMemoryState {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "MemoryState ...")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstRegisterState {
    /// the name of the unit
    pub name: Rc<String>,
    /// all the fields of this state
    pub fields: Vec<Rc<VelosiAstField>>,
    /// a map of strings to fields
    pub fields_map: HashMap<String, Rc<VelosiAstField>>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstRegisterState {
    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        _pt: VelosiParseTreeStateDef,
        _st: &mut SymbolTable,
    ) -> AstResult<VelosiAstState, VelosiAstIssues> {
        panic!("not implemented");
    }
}

/// Implementation of [Display] for [VelosiAstRegisterState]
impl Display for VelosiAstRegisterState {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "RegisterState ...")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiAstState {
    MemoryState(VelosiAstMemoryState),
    RegisterState(VelosiAstRegisterState),
    NoneState(VelosiTokenStream),
}

impl VelosiAstState {
    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeState,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        use VelosiParseTreeState::*;
        match pt {
            Memory(pt) => VelosiAstMemoryState::from_parse_tree(pt, st),
            Register(pt) => VelosiAstRegisterState::from_parse_tree(pt, st),
            None(ts) => AstResult::Ok(VelosiAstState::NoneState(ts)),
        }
    }

    pub fn name(&self) -> &str {
        "state"
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiAstState::MemoryState(s) => &s.loc,
            VelosiAstState::RegisterState(s) => &s.loc,
            VelosiAstState::NoneState(s) => s,
        }
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstState>> for Symbol {
    fn from(state: Rc<VelosiAstState>) -> Self {
        let ti = VelosiAstType::from(state.clone());
        let name = Rc::new(String::from("state"));
        Symbol::new(name, ti, VelosiAstNode::State(state))
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstState>> for VelosiAstType {
    fn from(c: Rc<VelosiAstState>) -> Self {
        VelosiAstType::new(VelosiAstTypeInfo::State, c.loc().clone())
    }
}

/// Implementation of [Display] for [VelosiAstState]
impl Display for VelosiAstState {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiAstState::MemoryState(s) => Display::fmt(s, f),
            VelosiAstState::RegisterState(s) => Display::fmt(s, f),
            VelosiAstState::NoneState(_) => writeln!(f, "NoneState"),
        }
    }
}
