// Velosiraptor Lexer
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

//! Unit Ast Node
//!
//! This defines a unit node in the AST. The unit node represents a unit definition,
//! and as such a type.

// the used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result};

// the used crate-internal functionality
use crate::ast::{
    utils, AstNode, AstNodeGeneric, Const, Flags, Interface, Issues, Method, Param, State, Symbol,
    SymbolKind, SymbolTable, Type,
};
use crate::error::{ErrorLocation, VrsError};
use crate::synth::Operation;
use crate::token::TokenStream;

use super::CFG_DEFAULT_BITWIDTH;

/// Represents a translation unit of the configurable segment type.
///
/// This type of translation unit remaps a contiguous region of memory
/// with a given size by adding a configurable offset to it.
#[derive(PartialEq, Eq, Clone)]
pub struct Segment {
    /// the name of the unit (identifier)
    pub name: String,
    /// the unit parameters
    pub params: Vec<Param>,
    /// the name of the derrived unit
    pub derived: Option<String>,
    /// the input bitwidth of the unit
    pub inbitwidth: u64,
    /// the output bitwidth of the unit
    pub outbitwidth: u64,
    /// defined constants in this unit
    pub consts: Vec<Const>,
    /// permission flags
    pub flags: Option<Flags>,
    /// the state of the unit
    pub state: State,
    /// the software visible interface of the unit
    pub interface: Interface,
    /// the methods defined by this unit
    pub methods: Vec<Method>,
    // TODO: maybe make the translate / constructors / map / ... explicit here?
    /// synthesized map operations for this unit
    pub map_ops: Option<Vec<Operation>>,
    /// synthesizeed unmap operations for this unit
    pub unmap_ops: Option<Vec<Operation>>,
    /// synthesized protect operations for this unit
    pub protect_ops: Option<Vec<Operation>>,
    /// the position in the source tree where this unit is defined
    pub pos: TokenStream,
}

/// Implementation of [Segment]
impl Segment {
    /// creates a new Segment node
    pub fn new(name: String, params: Vec<Param>, pos: TokenStream) -> Self {
        Segment {
            name,
            params,
            derived: None,
            inbitwidth: 0,
            outbitwidth: 0,
            consts: Vec::new(),
            flags: None,
            state: State::new_none(),
            interface: Interface::new_none(),
            methods: Vec::new(),
            map_ops: None,
            unmap_ops: None,
            protect_ops: None,
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

    pub fn set_state(mut self, state: State) -> Self {
        self.state = state;
        self
    }

    pub fn set_interface(mut self, interface: Interface) -> Self {
        self.interface = interface;
        self
    }

    pub fn add_consts(mut self, consts: Vec<Const>) -> Self {
        self.consts.extend(consts);
        self
    }

    pub fn set_flags(mut self, flags: Option<Flags>) -> Self {
        self.flags = flags;
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
            AstNode::Segment(self),
        )
    }

    /// Obtains the method with the given name
    pub fn get_method(&self, name: &str) -> Option<&Method> {
        self.methods.iter().find(|m| m.name == name)
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
        &self.interface
    }

    pub fn state(&self) -> &State {
        &self.state
    }

    pub fn map_ops(&self) -> Option<&Vec<Operation>> {
        self.map_ops.as_ref()
    }

    pub fn vaddr_max(&self) -> u64 {
        if self.inbitwidth < 64 {
            (1u64 << self.inbitwidth) - 1
        } else {
            u64::MAX
        }
    }

    pub fn paddr_max(&self) -> u64 {
        if self.outbitwidth < 64 {
            (1u64 << self.outbitwidth) - 1
        } else {
            u64::MAX
        }
    }

    /// derives [Self] from the other unit
    ///
    /// This pulls in the definitions, constants, etc from the other unit.
    /// Unit elements that are defined in [Self] will not be overwritten by the other unit.
    pub fn derive(&mut self, other: &Segment) {
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
    pub fn derives_from(&self, other: &Segment) -> Self {
        let mut u = self.clone();
        u.derive(other);
        u
    }
}

/// implementation of the [fmt::Display] trait for the [Segment]
impl Display for Segment {
    fn fmt(&self, f: &mut Formatter) -> Result {
        writeln!(f, "Segment {}", self.name)?;
        if let Some(d) = &self.derived {
            writeln!(f, " : {}", d)?;
        }
        writeln!(f, "{{\nTODO\n}}")
    }
}

/// implementation of the [fmt::Debug] trait for the [Segment]
impl Debug for Segment {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let line = self.loc().line();
        let column = self.loc().column();

        writeln!(f, "{:03}:{:03} | Segment {}", line, column, self.name)?;
        if let Some(d) = &self.derived {
            writeln!(f, " : {}", d)?;
        }
        writeln!(f, "{{\nTODO\n}}")
    }
}

/// Implemetation of the [AstNodeGeneric] trait for [Unit]
impl<'a> AstNodeGeneric<'a> for Segment {
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

        // add the state symbolds
        // XXX: maybe we wan to do the symbol table building after checking the elements?
        self.state.build_symboltable(st);
        self.interface.build_symboltable(st);

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

        // Check 3: State Check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the state definition is fine
        // Notes:       --
        // --------------------------------------------------------------------------------------

        if self.state.is_none() {
            let msg = format!("missing state definition for unit `segment {}`", self.name);
            let hint = String::from("add the state definition `state = Register | Memory` here");
            VrsError::new_err(self.pos.with_range(0..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        // check the state and interface
        res = res + self.state.check(st);

        // Check 4: State Param Check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the state refers to actual parameters
        // Notes:       --
        // --------------------------------------------------------------------------------------
        // TODO: check params

        // Check 5: Interface Check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the state definition is fine
        // Notes:       --
        // --------------------------------------------------------------------------------------

        if self.interface.is_none() {
            let msg = format!(
                "missing interface definition for unit `segment {}`",
                self.name
            );
            let hint =
                String::from("add the interface definition `interface = Register | Memory` here");
            VrsError::new_err(self.pos.with_range(0..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        res = res + self.interface.check(st);

        // Check 6: Interface param check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the interface refers to actual parameters
        // Notes:       --
        // --------------------------------------------------------------------------------------
        // TODO: check params / field refs

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
            // create a new symbol table context
            st.create_context(m.name.clone());

            if let Some(f) = &self.flags {
                for p in m.get_flag_params() {
                    f.build_symboltable(p, st);
                }
            }

            res = res + m.check(st);

            if !st.insert(m.to_symbol()) {
                res.inc_err(1);
            }

            // restore the symbol table again
            st.drop_context();
        }

        // Check 9: Bases are defined
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: Check if the unit name is CamelCase
        // Notes:       --
        // --------------------------------------------------------------------------------------
        res = res + utils::check_camel_case(name, pos);

        // Check 10: Translate/Map methods defined
        // --------------------------------------------------------------------------------------
        // Type:        Error/Warning
        // Description: Check all defined constats of the Unit
        // Notes:
        // --------------------------------------------------------------------------------------

        let mut has_map = false;
        let mut has_translate = false;
        let mut has_matchflags = false;
        for m in &self.methods {
            match m.name() {
                "translate" => {
                    has_translate = true;
                }
                "map" => {
                    has_map = true;
                }
                "matchflags" => {
                    has_matchflags = true;
                }
                "remap" => {}
                _ => {}
            }
        }

        if !has_translate {
            let msg = format!("translate() method not defined for unit `{}`", name);
            let hint = format!("implement the translate() method for unit `{}`", name);
            VrsError::new_err(pos.with_range(0..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        if !has_matchflags {
            let msg = format!("matchflags() method not defined for unit `{}`", name);
            let hint = format!("implement the matchflags() method for unit `{}`", name);
            VrsError::new_err(pos.with_range(0..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        if !has_map {
            let msg = format!("map() method not defined for unit `{}`", name);
            let hint = format!("implement the map() method for unit `{}`", name);
            VrsError::new_err(pos.with_range(0..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        st.drop_context();
        res
    }

    fn rewrite(&'a mut self) {
        println!("rewriting segment {}", self.name);
        for c in &mut self.consts {
            c.rewrite();
        }

        for m in &mut self.methods {
            m.rewrite();
        }
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        &self.pos
    }

    fn name(&self) -> &str {
        self.name.as_str()
    }
}
