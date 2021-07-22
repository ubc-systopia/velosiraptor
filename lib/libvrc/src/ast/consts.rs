// Velosiraptor ParseTree
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

//! Ast Module of the Velosiraptor Compiler

use crate::sourcepos::SourcePos;
use std::fmt;

/// Defines a [Constant] statement node
///
/// The constants statement defines and delcares specific symbols
/// with constant values to be used throughout the definitions.
///
/// The constant can be defined as part of the file global definitions
/// or within a unit context.
#[derive(PartialEq, Clone)]
pub enum Const {
    /// Represents an integer constant.
    ///
    /// This corresponds to an Integer literal
    Integer {
        ident: String,
        value: u64,
        pos: SourcePos,
    },
    /// Represents an boolean constant
    ///
    /// This corresponds to an Boolean literal
    Boolean {
        ident: String,
        value: bool,
        pos: SourcePos,
    }, // TODO: add address / size constants here as well?
}

impl Const {
    pub fn pos(&self) -> &SourcePos {
        use self::Const::*;
        match self {
            Integer {
                ident: _,
                value: _,
                pos,
            } => &pos,
            Boolean {
                ident: _,
                value: _,
                pos,
            } => &pos,
        }
    }

    pub fn ident(&self) -> &str {
        use self::Const::*;
        match self {
            Integer {
                ident,
                value: _,
                pos: _,
            } => &ident,
            Boolean {
                ident,
                value: _,
                pos: _,
            } => &ident,
        }
    }
}

/// implementation of the [fmt::Display] trait for the [Const]
impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Const::*;
        match self {
            Integer {
                ident,
                value,
                pos: _,
            } => writeln!(f, "const {} : int  = {};", ident, value),
            Boolean {
                ident,
                value,
                pos: _,
            } => writeln!(f, "const {} : bool = {};", ident, value),
        }
    }
}

/// implementation of the [fmt::Debug] trait for the [Const]
impl fmt::Debug for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Const::*;
        match self {
            Integer { ident, value, pos } => {
                let (line, column) = pos.input_pos();
                writeln!(
                    f,
                    "{:03}:{:03} | const {} :  int = {};",
                    line, column, ident, value
                )
            }
            Boolean { ident, value, pos } => {
                let (line, column) = pos.input_pos();
                writeln!(
                    f,
                    "{:03}:{:03} | const {} : bool = {};",
                    line, column, ident, value
                )
            }
        }
    }
}

use crate::ast::{AstCheck, CheckResult};
use crate::error::{ErrorType, VrsError};
impl AstCheck for Const {
    fn check(&self) -> CheckResult {
        use self::Const::*;
        let (name, pos) = match &self {
            Integer {
                ident,
                value: _,
                pos,
            } => (ident, pos),
            Boolean {
                ident,
                value: _,
                pos,
            } => (ident, pos),
        };

        // issue warning
        if !name.is_ascii() {
            let msg = format!("constant `{}` should have an upper case name", name);
            let hint = format!(
                "help: convert the identifier to upper case (notice the capitalization): `{}`",
                name.to_ascii_uppercase()
            );
            VrsError::new_warn(pos, msg, Some(hint)).print();
            return CheckResult::Error;
        }

        let allupper = name
            .as_bytes()
            .iter()
            .fold(true, |acc, x| acc & x.is_ascii_uppercase());
        if !allupper {
            let msg = format!("constant `{}` should have an upper case name", name);
            let hint = format!(
                "help: convert the identifier to upper case (notice the capitalization): `{}`",
                name.to_ascii_uppercase()
            );
            VrsError::new_warn(pos, msg, Some(hint)).print();
            // warning
            return CheckResult::Warning;
        }
        CheckResult::Ok
    }
}
