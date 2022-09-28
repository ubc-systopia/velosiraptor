// Velosiraptor Lexer
//
//
// MIT License
//
// Copyright (c) 2021,2022 Systopia Lab, Computer Science, University of British Columbia
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

//! Unit Ast Node
//!
//! This defines a unit node in the AST. The unit node represents a unit definition,
//! and as such a type.

// the used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result};

// the used crate-internal functionality
use crate::ast::{
    utils, AstNode, AstNodeGeneric, Const, Interface, Issues, Map, Method, Param, State, Symbol,
    SymbolKind, SymbolTable, Type,
};
use crate::error::ErrorLocation;
use crate::synth::Operation;
use crate::token::TokenStream;

use super::CFG_DEFAULT_BITWIDTH;

/// Rep
#[derive(PartialEq, Eq, Clone)]
pub struct StaticMap {
    /// the name of the unit (identifier)
    pub name: String,
    /// the unit parameters
    pub params: Vec<Param>,
    /// the name of the derived unit
    pub derived: Option<String>,
    /// the input bit width of the unit
    pub inbitwidth: u64,
    /// the outbit width with of the unit
    pub outbitwidth: u64,
    /// defined constants in this unit
    pub consts: Vec<Const>,
    /// Optional map in the case of map UnitType
    pub map: Option<Map>,
    /// the methods defined by this unit
    pub methods: Vec<Method>,
    /// the position in the source tree where this unit is defined
    pub pos: TokenStream,
}

/// Implementation of [Unit]
impl StaticMap {
    /// creates a new Segment node
    pub fn new(name: String, params: Vec<Param>, pos: TokenStream) -> Self {
        StaticMap {
            name,
            params,
            derived: None,
            inbitwidth: 0,
            outbitwidth: 0,
            consts: Vec::new(),
            methods: Vec::new(),
            map: None,
            pos,
        }
    }

    /// sets the input addressing bit width
    pub fn set_inbitwidth(mut self, inbitwidth: Option<u64>) -> Self {
        self.inbitwidth = inbitwidth.unwrap_or(CFG_DEFAULT_BITWIDTH);
        self
    }

    /// sets the output addressing bit width
    pub fn set_outbitwidth(mut self, outbitwidth: Option<u64>) -> Self {
        self.outbitwidth = outbitwidth.unwrap_or(CFG_DEFAULT_BITWIDTH);
        self
    }

    pub fn set_derived(mut self, derived: Option<String>) -> Self {
        self.derived = derived;
        self
    }

    pub fn set_map(mut self, map: Map) -> Self {
        self.map = Some(map);
        self
    }

    pub fn add_consts(mut self, consts: Vec<Const>) -> Self {
        self.consts.extend(consts);
        self
    }

    pub fn add_methods(mut self, methods: Vec<Method>) -> Self {
        self.methods.extend(methods);
        self
    }

    /// finalized the unit
    pub fn finalize(mut self, pos: &TokenStream) -> Self {
        self.pos = self.pos.expand_until(pos);
        self
    }

    pub fn location(&self) -> String {
        self.pos.location()
    }

    pub fn to_symbol(&self) -> Symbol {
        Symbol::new(
            self.name.clone(),
            Type::Unit,
            SymbolKind::Unit,
            self.loc().clone(),
            AstNode::StaticMap(self),
        )
    }

    /// Obtains the derived element of the segment if any
    pub fn derived(&self) -> Option<&String> {
        self.derived.as_ref()
    }

    pub fn methods(&self) -> &[Method] {
        &self.methods
    }

    pub fn consts(&self) -> &[Const] {
        &self.consts
    }

    pub fn interface(&self) -> &Interface {
        &crate::ast::NONE_INTERFACE
    }

    pub fn state(&self) -> &State {
        &crate::ast::NONE_STATE
    }

    pub fn map_ops(&self) -> Option<&Vec<Operation>> {
        None
    }

    pub fn vaddr_max(&self) -> u64 {
        todo!("need to figure out teh maps first");
    }
    pub fn paddr_max(&self) -> u64 {
        todo!("need to figure out teh maps first");
    }

    /// derives [Self] from the other unit
    ///
    /// This pulls in the definitions, constants, etc from the other unit.
    /// Unit elements that are defined in [Self] will not be overwritten by the other unit.
    pub fn derive(&mut self, other: &StaticMap) {
        assert!(self.derived.is_some());
        assert_eq!(self.derived.as_ref().unwrap(), other.name.as_str());
        println!("unit: {} deriving form {}", self.name, other.name());

        // merge params
        for p in other.params.iter() {
            if !self.params.iter().any(|x| x.name == p.name) {
                self.params.push(p.clone());
            }
        }

        // merge methods
        for m in other.methods.iter() {
            if !self.methods.iter().any(|x| x.name == m.name) {
                self.methods.push(m.clone());
            }
        }
        // merge interface

        // merge state
    }

    /// derives a new unit from self and another unit
    pub fn derives_from(&self, other: &StaticMap) -> Self {
        let mut u = self.clone();
        u.derive(other);
        u
    }
}

/// implementation of the [fmt::Display] trait for the [StaticMap]
impl Display for StaticMap {
    fn fmt(&self, f: &mut Formatter) -> Result {
        writeln!(f, "StaticMap {}", self.name)?;
        if let Some(d) = &self.derived {
            writeln!(f, " : {}", d)?;
        }
        writeln!(f, "{{\nTODO\n}}")
    }
}

/// implementation of the [fmt::Debug] trait for the [StaticMap]
impl Debug for StaticMap {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let line = self.loc().line();
        let column = self.loc().column();

        writeln!(f, "{:03}:{:03} | StaticMap {}", line, column, self.name)?;
        if let Some(d) = &self.derived {
            writeln!(f, " : {}", d)?;
        }
        writeln!(f, "{{\nTODO\n}}")
    }
}

/// Implemetation of the [AstNodeGeneric] trait for [StaticMap]
impl<'a> AstNodeGeneric<'a> for StaticMap {
    /// performs the ast checks for the StaticMap
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        // all fine for now
        let mut res = Issues::ok();

        let name = self.name();
        let pos = self.loc();

        // set the current context
        st.create_context(String::from(self.name()));

        // adding the module paramters
        for p in &self.params {
            if !st.insert(p.to_symbol()) {
                res.inc_err(1);
            }
        }

        // NOTE: we do not add the constants and methods to the symbol table here

        // Check 1: Double defined constants
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that all constants of this field have distinct names
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let errors = utils::check_double_entries(&self.consts);
        res.inc_err(errors);

        // Check 2: Constants
        // --------------------------------------------------------------------------------------
        // Type:        Error/Warning
        // Description: Check all defined constats of the Unit
        // Notes:
        // --------------------------------------------------------------------------------------
        for c in &self.consts {
            res = res + c.check(st);

            if !st.insert(c.to_symbol()) {
                res.inc_err(1);
            }
        }

        // Check 3: Map definition
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check the static map definition
        // Notes:
        // --------------------------------------------------------------------------------------
        if let Some(m) = &self.map {
            res = res + m.check(st);
        }

        // Check 4: State Param Check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the state refers to actual parameters
        // Notes:       --
        // --------------------------------------------------------------------------------------
        // TODO: check params

        // Check 7: Methods double defined
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check double method definition
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let errors = utils::check_double_entries(&self.methods);
        res.inc_err(errors);

        // Check 8: Method check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the interface refers to actual parameters
        // Notes:       --
        // --------------------------------------------------------------------------------------

        for m in &self.methods {
            res = res + m.check(st);

            if !st.insert(m.to_symbol()) {
                res.inc_err(1);
            }
        }

        // Check 9: Bases are defined
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: Check if the unit name is CamelCase
        // Notes:       --
        // --------------------------------------------------------------------------------------
        res = res + utils::check_camel_case(name, pos);

        st.drop_context();
        res
    }

    /// returns the location of the StaticMap
    fn loc(&self) -> &TokenStream {
        &self.pos
    }

    /// returns the name of the StaticName
    fn name(&self) -> &str {
        self.name.as_str()
    }
}
