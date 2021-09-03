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
use crate::ast::{utils, AstNode, Const, Interface, Issues, Method, State, SymbolTable};
use crate::error::ErrorLocation;
use crate::token::TokenStream;

/// Defines a translation unit
///
/// A translation unit describes a translation unit and consists of multiple
/// components that from the personality of the translation unit.
///
/// Moreover, a translation unit may be derived from another unit, similar
/// to inheritance in other languages.
#[derive(PartialEq, Clone)]
pub struct Unit {
    /// the name of the unit (identifier)
    pub name: String,
    /// the name of the derrived unit
    pub derived: Option<String>,
    /// the size of the unit in bits
    pub size: Option<u64>,
    /// defined constants in this unit
    pub consts: Vec<Const>,
    /// the state of the unit
    pub state: State,
    /// the software visible interface of the unit
    pub interface: Interface,
    /// the methods defined by this unit
    pub methods: Vec<Method>,
    // TODO: maybe make the translate / constructors / map / ... explicit here?
    /// the position in the source tree where this unit is defined
    pub pos: TokenStream,
}

/// Implementation of [Unit]
impl Unit {
    pub fn location(&self) -> String {
        self.pos.location()
    }
}

/// Implemetation of the [AstNode] trait for [Unit]
impl AstNode for Unit {
    fn check(&self, st: &mut SymbolTable) -> Issues {
        // all fine for now
        let mut res = Issues::ok();

        let name = self.name();
        let pos = self.loc();

        // set the current context
        st.set_context(self.name());

        // Check 1: Constants
        // --------------------------------------------------------------------------------------
        // Type:        Error/Warning
        // Description: Check all defined constats of the Unit
        // Notes:
        // --------------------------------------------------------------------------------------
        for c in &self.consts {
            res = res + c.check(st);
        }

        // Check 2: Double defined constants
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that all constants of this field have distinct names
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let errors = utils::check_double_entries(&self.consts);
        res.inc_err(errors);

        // Check 3: State Check
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the state definition is fine
        // Notes:       --
        // --------------------------------------------------------------------------------------

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

        res = res + self.state.check(st);

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

        // let errors = utils::check_double_entries(&self.methods);
        // res.inc_err(errors);

        // Check 8: Method cehck
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Error
        // Description: Check that the interface refers to actual parameters
        // Notes:       --
        // --------------------------------------------------------------------------------------

        // for m in &self.methods {
        //     res = res + m.check(st);
        // }

        // Check 9: Bases are defined
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: Check if the unit name is CamelCase
        // Notes:       --
        // --------------------------------------------------------------------------------------
        res + utils::check_camel_case(name, pos)
    }
    ///
    fn name(&self) -> &str {
        &self.name
    }
    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        &self.pos
    }

    // builds the symbol table
    fn build_symtab(&self, st: &mut SymbolTable) -> Issues {
        let mut err = Issues::ok();
        for i in &self.consts {
            let sym = i.to_symbol(&self.name());
            if st.insert(sym).is_err() {
                err.inc_err(1);
            };
        }
        err
    }
}

/// implementation of the [fmt::Display] trait for the [Unit]
impl Display for Unit {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match &self.derived {
            Some(n) => writeln!(f, "Unit {} : {}  {{\nTODO\n}}", self.name, n),
            None => writeln!(f, "Unit {} {{\nTODO\n}}", self.name),
        }
    }
}

/// implementation of the [fmt::Debug] trait for the [Unit]
impl Debug for Unit {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let line = self.loc().line();
        let column = self.loc().column();
        match &self.derived {
            Some(n) => writeln!(
                f,
                "{:03}:{:03} | unit {} : {}  {{\nTODO\n}}",
                line, column, self.name, n
            ),
            None => writeln!(
                f,
                "{:03}:{:03} | unit {} {{\nTODO\n}}",
                line, column, self.name
            ),
        }
    }
}

/// implementation of [PartialOrd] for [Import]
impl PartialOrd for Unit {
    /// This method returns an ordering between self and other values if one exists.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // we jus compare with the TokenStream position
        self.loc().partial_cmp(&other.loc())
    }
}
