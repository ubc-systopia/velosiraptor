// Velosiraptor Lexer
//
//
// MIT License
//
// Copyright (c) 2021 Systopia Lab, Computer Science, University of British Columbia
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
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter, Result};

// the used crate-internal functionality
use crate::ast::{
    utils, AstNode, AstNodeGeneric, Const, Interface, Issues, Map, Method, Param, State, Symbol,
    SymbolKind, SymbolTable, Type,
};
use crate::error::{ErrorLocation, VrsError};
use crate::synth::Operation;
use crate::token::TokenStream;

/// Defines a translation unit
///
/// A translation unit describes a translation unit and consists of multiple
/// components that from the personality of the translation unit.
///
/// Moreover, a translation unit may be derived from another unit, similar
/// to inheritance in other languages.
#[derive(PartialEq, Clone)]
pub enum Unit {
    StaticMap {
        /// the name of the unit (identifier)
        name: String,
        /// the unit parameters
        params: Vec<Param>,
        /// the name of the derived unit
        derived: String,
        /// the size of the unit in bits
        size: Option<u64>,
        /// defined constants in this unit
        consts: Vec<Const>,
        /// Optional map in the case of map UnitType
        map: Option<Map>,
        /// the position in the source tree where this unit is defined
        pos: TokenStream,
    },
    Segment {
        /// the name of the unit (identifier)
        name: String,
        /// the unit parameters
        params: Vec<Param>,
        /// the name of the derrived unit
        derived: String,
        /// the size of the unit in bits
        size: Option<u64>,
        /// defined constants in this unit
        consts: Vec<Const>,
        /// the state of the unit
        state: State,
        /// the software visible interface of the unit
        interface: Interface,
        /// the methods defined by this unit
        methods: Vec<Method>,
        // TODO: maybe make the translate / constructors / map / ... explicit here?
        /// synthesized map operations for this unit
        map_ops: Option<Vec<Operation>>,
        /// synthesizeed unmap operations for this unit
        unmap_ops: Option<Vec<Operation>>,
        /// synthesized protect operations for this unit
        protect_ops: Option<Vec<Operation>>,
        /// the position in the source tree where this unit is defined
        pos: TokenStream,  
    }
}

/// Implementation of [Unit]
impl<'a> Unit {

    pub fn location(&self) -> String {
        match self {
            Unit::StaticMap { pos, ..  } => pos.location(),
            Unit::Segment { pos, .. } => pos.location()
        } 
    }

    pub fn to_symbol(&self) -> Symbol {
        let name = match self {
            Unit::StaticMap { name, .. } => name.clone(),
            Unit::Segment { name, .. } => name.clone(),
        };
        
        Symbol::new(
            name, 
            Type::Unit,
            SymbolKind::Unit,
            self.loc().clone(),
            AstNode::Unit(self),
        )
    }

    /// obtains a method with a given anme
    pub fn get_method(&self, name: &str) -> Option<&Method> {
        // TODO: make this a hashmap!
        let methods = match self {
            Unit::StaticMap { .. } => todo!(),
            Unit::Segment { methods, .. } => methods,
        };
        for m in methods.iter() {
            if m.name == name {
                return Some(m);
            }
        }
        None
    }

    pub fn derived(&self) -> &str {
        match self {
            Unit::StaticMap { derived, .. } => &derived,
            Unit::Segment { derived, .. } => &derived,
        }
    }

}

/// Implemetation of the [AstNodeGeneric] trait for [Unit]
impl<'a> AstNodeGeneric<'a> for Unit {
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        match self {
            Unit::StaticMap { 
                name, pos, params, derived, size, consts, map, 
            } => {
                todo!();
            }
            Unit::Segment { 
                name, params, derived, size, consts, state, interface, methods, map_ops, unmap_ops, protect_ops, pos 
            } => {
                // all fine for now
                let mut res = Issues::ok();

                let name = self.name();
                let pos = self.loc();

                // set the current context
                st.create_context(String::from(self.name()));

                // adding the module paramters
                for p in params {
                    if !st.insert(p.to_symbol()) {
                        res.inc_err(1);
                    }
                }

                // adding the constants
                for c in consts {
                    if !st.insert(c.to_symbol()) {
                        res.inc_err(1);
                    }
                }

                // add the methods to it
                for m in methods {
                    if !st.insert(m.to_symbol()) {
                        res.inc_err(1);
                    }
                }

                // add the state symbolds
                // XXX: maybe we wan to do the symbol table building after checking the elements?
                state.build_symboltable(st);
                interface.build_symboltable(st);

                // Check 1: Double defined constants
                // --------------------------------------------------------------------------------------
                // Type:        Error
                // Description: Check that all constants of this field have distinct names
                // Notes:       --
                // --------------------------------------------------------------------------------------

                let errors = utils::check_double_entries(consts);
                res.inc_err(errors);

                // Check 2: Constants
                // --------------------------------------------------------------------------------------
                // Type:        Error/Warning
                // Description: Check all defined constats of the Unit
                // Notes:
                // --------------------------------------------------------------------------------------
                for c in consts {
                    res = res + c.check(st);
                }

                // Check 3: State Check
                // --------------------------------------------------------------------------------------
                // Type:        Warning/Error
                // Description: Check that the state definition is fine
                // Notes:       --
                // --------------------------------------------------------------------------------------

                // check the state and interface
                res = res + state.check(st);

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
                res = res + interface.check(st);

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

                let errors = utils::check_double_entries(methods);
                res.inc_err(errors);

                // Check 8: Method check
                // --------------------------------------------------------------------------------------
                // Type:        Warning/Error
                // Description: Check that the interface refers to actual parameters
                // Notes:       --
                // --------------------------------------------------------------------------------------

                for m in methods {
                    res = res + m.check(st);
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
                for m in methods {
                    match m.name() {
                        "translate" => {
                            res = res + m.check_translate();
                            has_translate = true;
                        }
                        "map" => {
                            res = res + m.check_map();
                            has_map = true;
                        }
                        _ => {}
                    }
                }

                if !has_translate {
                    let msg = format!("translate() method not defined for unit `{}`", name);
                    let hint = format!("implement the translate() method for unit `{}`", name);
                    VrsError::new_err(pos.with_range(0..2), msg, Some(hint)).print();
                    res.inc_err(1);
                }
                if !has_map {
                    let msg = format!("map() method not defined for unit `{}`", name);
                    let hint = format!("implement the map() method for unit `{}`", name);
                    VrsError::new_err(pos.with_range(0..2), msg, Some(hint)).print();
                    println!("{}", pos);
                    res.inc_err(1);
                }

                st.drop_context();
                res
            }
        }
        
    }
    ///
    fn name(&self) -> &str {
        match self {
            Unit::StaticMap { name, .. } => &name,
            Unit::Segment { name, .. } => &name,
        }
    }
    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        match self {
            Unit::Segment { pos, .. } => &pos,
            Unit::StaticMap { pos, .. } => &pos,
        }
    }
}

/// implementation of the [fmt::Display] trait for the [Unit]
impl Display for Unit {
    fn fmt(&self, f: &mut Formatter) -> Result {
        writeln!(f, "Unit {} : {}  {{\nTODO\n}}", self.name(), self.derived())
    }
}

/// implementation of the [fmt::Debug] trait for the [Unit]
impl Debug for Unit {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let line = self.loc().line();
        let column = self.loc().column();
        writeln!(
            f,
            "{:03}:{:03} | unit {} : {}  {{\nTODO\n}}",
            line, column, self.name(), self.derived()
        )
    }
}

/// implementation of [PartialOrd] for [Import]
impl PartialOrd for Unit {
    /// This method returns an ordering between self and other values if one exists.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // we jus compare with the TokenStream position
        self.loc().partial_cmp(other.loc())
    }
}
