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

//! Constant Ast Node
//!
//! This defines a constant node in the AST. The constant node represents a
//! defined constant either in the file or unit context

// the used standard library functionality
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter, Result};

// the used crate-internal functionality
use crate::ast::{AstNode, Expr, Issues};
use crate::error::VrsError;
use crate::token::TokenStream;

/// Defines a [Const] statement node
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
        value: Expr,
        pos: TokenStream,
    },
    /// Represents an boolean constant
    ///
    /// This corresponds to an Boolean literal
    Boolean {
        ident: String,
        value: Expr,
        pos: TokenStream,
    }, // TODO: add address / size constants here as well?
}

impl Const {
    /// returns the expression that defines the value
    pub fn value(&self) -> &Expr {
        use self::Const::*;
        match self {
            Integer {
                ident: _,
                value,
                pos: _,
            } => &value,
            Boolean {
                ident: _,
                value,
                pos: _,
            } => &value,
        }
    }
}

/// implementation of the [Display] trait for the [Const]
impl Display for Const {
    fn fmt(&self, f: &mut Formatter) -> Result {
        use self::Const::*;
        match self {
            Integer {
                ident,
                value,
                pos: _,
            } => write!(f, "const {} : int  = {};", ident, value),
            Boolean {
                ident,
                value,
                pos: _,
            } => write!(f, "const {} : bool = {};", ident, value),
        }
    }
}

/// implementation of the [Debug] trait for the [Const]
impl Debug for Const {
    fn fmt(&self, f: &mut Formatter) -> Result {
        use self::Const::*;
        match self {
            Integer { ident, value, pos } => {
                let (line, column) = pos.input_sourcepos().input_pos();
                write!(
                    f,
                    "{:03}:{:03} | const {} :  int = {:?};, {:?}",
                    line, column, ident, value, pos
                )
            }
            Boolean { ident, value, pos } => {
                let (line, column) = pos.input_sourcepos().input_pos();
                write!(
                    f,
                    "{:03}:{:03} | const {} : bool = {};",
                    line, column, ident, value
                )
            }
        }
    }
}

/// implementation of [PartialOrd] for [Const]
impl PartialOrd for Const {
    /// This method returns an ordering between self and other values if one exists.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // we jus compare with the TokenStream position
        self.loc().partial_cmp(&other.loc())
    }
}

/// implementation of [AstNode] for [Const]
impl AstNode for Const {
    fn check(&self) -> Issues {
        let mut res = Issues::ok();

        let name = self.name();
        let pos = self.loc();
        let val = self.value();
        if !val.is_const_expr() {
            let msg = String::from("not a constant expression");
            let hint = String::from("convert the expression to a constant");
            VrsError::new_err(val.loc(), msg, Some(hint)).print();

            res = res + Issues::err();
        }

        // issue warning
        if !name.is_ascii() {
            let msg = format!("constant `{}` should have an upper case name", name);
            let hint = format!(
                "convert the identifier to ASCII: `{}`",
                name.to_ascii_uppercase()
            );
            VrsError::new_warn(pos.with_range(1..2), msg, Some(hint)).print();
            res = res + Issues::warn();
        }

        let allupper = name
            .as_bytes()
            .iter()
            .fold(true, |acc, x| acc & !x.is_ascii_lowercase());
        if !allupper {
            let msg = format!("constant `{}` should have an upper case name", name);
            let hint = format!(
                "convert the identifier to upper case (notice the capitalization): `{}`",
                name.to_ascii_uppercase()
            );
            VrsError::new_warn(pos.with_range(1..2), msg, Some(hint)).print();
            // warning
            res = res + Issues::warn();
        }
        res
    }

    fn name(&self) -> &str {
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

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
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
}
