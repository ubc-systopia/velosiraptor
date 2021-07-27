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
use crate::error::{ErrorLocation, VrsError};
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
impl Unit {}

/// Implemetation of the [AstNode] trait for [Unit]
impl AstNode for Unit {
    fn check(&self) -> Issues {
        // all fine for now
        let mut res = Issues::ok();

        let name = self.name();
        let pos = self.loc();

        // name should start with upper case
        if !name[0..1].as_bytes()[0].is_ascii_uppercase() {
            let msg = format!("unit `{}` should start with an uppercase letter", name);
            let mut name = String::from(name);
            name[0..1].make_ascii_uppercase();
            let hint = format!(
                "convert the identifier to upper case (notice the capitalization): `{}`",
                name
            );
            VrsError::new_warn(pos.with_range(1..2), msg, Some(hint)).print();
            res = res + Issues::warn();
        }

        // check if there are any double entries in the constants, and check the constants
        let errors = utils::check_double_entries(&self.consts);
        res.inc_err(errors);
        for c in &self.consts {
            res = res + c.check();
        }

        // check the state and interface
        res = res + self.state.check();

        //todo!("check interface");
        //res = res += self.interface.check();

        // check if there are any double entries in the methods, and check the constants
        //todo!("check methods");
        // let errors = utils::check_double_entries(&self.methods);
        // res.inc_err(errors);
        // for m in &self.methods {
        //     res = res + m.check();
        // }
        res
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
