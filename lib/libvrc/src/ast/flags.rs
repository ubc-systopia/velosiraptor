// Velosiraptor Compiler
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! Flag ASTNode
//!
//! Represents access flags

// std library imports
use std::fmt::{Debug, Display, Formatter, Result};

use crate::ast::{utils, AstNode, AstNodeGeneric, Issues, Symbol, SymbolKind, SymbolTable, Type};
use crate::error::{ErrorLocation, VrsError};
use crate::token::TokenStream;

/// represent a flag value
#[derive(PartialEq, Eq, Clone)]
pub struct Flag {
    /// the name of the flag
    pub name: String,
    /// the location where the action was defined
    pub pos: TokenStream,
}

impl Flag {
    pub fn new(name: String, pos: TokenStream) -> Self {
        Flag { name, pos }
    }

    pub fn finalize(mut self, pos: &TokenStream) -> Self {
        self.pos = self.pos.expand_until(pos);
        self
    }

    pub fn to_symbol(&self, varname: &str) -> Symbol {
        let name = format!("{}.{}", varname, self.name);
        Symbol::new(
            name,
            Type::Boolean,
            SymbolKind::Parameter,
            self.pos.clone(),
            AstNode::Flag(self),
        )
    }
}

/// Implementation of the [Display] trait for [Flag]
impl Display for Flag {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{},", self.name)
    }
}

/// Implementation of the [Debug] trait for [Flag]
impl Debug for Flag {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let column = self.pos.column();
        let line = self.pos.line();
        write!(f, "{:03}:{:03} | {},", line, column, self.name)
    }
}

/// implementation of [AstNodeGeneric] for [BitSlice]
impl<'a> AstNodeGeneric<'a> for Flag {
    fn check(&self, _st: &mut SymbolTable) -> Issues {
        let mut res = Issues::ok();

        // Check 1: Identifier is ASCII
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: The name of the flag must be in ASCII characters.
        // Notes:       --
        // --------------------------------------------------------------------------------------

        if !self.name.is_ascii() {
            let msg = format!("flags `{}` should be in ASCII", self.name);
            let hint = format!(
                "convert the identifier to ASCII: `{}`",
                self.name.to_ascii_uppercase()
            );
            VrsError::new_err(self.pos.with_range(1..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        // Check 2: Identifier format
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: The identifier should be in `CAPITAL_SNAKE_CASE`.
        // Notes:       We test for double defined slices in the parent node.
        // --------------------------------------------------------------------------------------

        res = res + utils::check_snake_case(&self.name, &self.pos);

        // Check 3: Value popcount
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: The value of the flag should be a power of two
        // Notes:       Maybe that's not needed
        // --------------------------------------------------------------------------------------

        // if self.value == 0 {
        //     let msg = format!("flags `{}` has a zero value", self.name);
        //     let hint = String::from("use a non-zero value for the flags here.");
        //     VrsError::new_err(self.pos.with_range(2..3), msg, Some(hint)).print();
        //     res.inc_err(1);
        // } else if self.value & (self.value - 1) != 0 {
        //     let msg = format!("flags `{}` has a non-power-of-two value", self.name);
        //     let hint = String::from("use a power-of-two value for the flags here.");
        //     VrsError::new_warn(self.pos.with_range(2..3), msg, Some(hint)).print();
        //     res.inc_warn(1);
        // }

        res
    }

    /// returns the name of the node
    fn name(&self) -> &str {
        &self.name
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        &self.pos
    }
}

/// represent a flag value
#[derive(PartialEq, Eq, Clone)]
pub struct Flags {
    /// the flags defined in this node
    pub flags: Vec<Flag>,
    /// the location where the action was defined
    pub pos: TokenStream,
}

impl<'a> Flags {
    pub fn new(pos: TokenStream) -> Self {
        Flags {
            flags: Vec::new(),
            pos,
        }
    }

    pub fn add_flags(mut self, flags: Vec<Flag>) -> Self {
        self.flags.extend(flags);
        self
    }

    pub fn finalize(mut self, pos: &TokenStream) -> Self {
        self.pos = self.pos.expand_until(pos);
        self
    }

    pub fn to_symbol(&self) -> Symbol {
        let name = "type!flags".to_string();
        Symbol::new(
            name,
            Type::Flags,
            SymbolKind::Flags,
            self.pos.clone(),
            AstNode::Flags(self),
        )
    }

    /// builds the symboltable for the state related symbols
    pub fn build_symboltable(&'a self, varname: &str, st: &mut SymbolTable<'a>) {
        for flag in &self.flags {
            st.insert(flag.to_symbol(varname));
        }
    }
}

/// Implementation of the [Display] trait for [Flag]
impl Display for Flags {
    fn fmt(&self, f: &mut Formatter) -> Result {
        writeln!(f, "flags = {{")?;
        for flag in &self.flags {
            writeln!(f, "    {}", flag)?;
        }
        writeln!(f, "}}")
    }
}

/// Implementation of the [Debug] trait for [Flag]
impl Debug for Flags {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let column = self.pos.column();
        let line = self.pos.line();
        writeln!(f, "{:03}:{:03} | flags = {{", line, column)?;
        for flag in &self.flags {
            writeln!(f, "    {}", flag)?;
        }
        writeln!(f, "}}")
    }
}

/// implementation of [AstNodeGeneric] for [BitSlice]
impl<'a> AstNodeGeneric<'a> for Flags {
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        let mut res = Issues::ok();

        // Check 1: Check individual flags
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check the flags
        // Notes:       --
        // --------------------------------------------------------------------------------------

        for f in &self.flags {
            res = res + f.check(st);
        }

        // Check 2: Double defined flags
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: The name of the bitslice must be in ASCII characters.
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let errors = utils::check_double_entries(&self.flags);
        res.inc_err(errors);
        res
    }

    /// returns the name of the node
    fn name(&self) -> &str {
        "flags"
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        &self.pos
    }
}
