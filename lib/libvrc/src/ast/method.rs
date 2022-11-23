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

use std::collections::HashSet;
///! Method module
// std lib imports
use std::fmt;

use crate::ast::{
    utils, AstNode, AstNodeGeneric, Expr, Issues, Param, Stmt, Symbol, SymbolKind, SymbolTable,
    Type,
};
use crate::error::VrsError;
use crate::token::TokenStream;



/// Defines a Method inside a unit
///
/// A method defines certain functionality of the translation unit.
///
/// # Examples
///
///  - Translate(): a method that translates an address (required)
///  - get_size(): a method that extracts the
#[derive(PartialEq, Eq, Clone)]
pub struct Method {
    /// the name of the method
    pub name: String,
    /// the return type of the method
    pub rettype: Type,
    /// A list of arguments with their types
    pub args: Vec<Param>,
    /// the ensures clauses
    pub requires: Vec<Expr>,
    /// the ensures clauses
    pub ensures: Vec<Expr>,
    /// the statements in the method
    pub stmts: Option<Stmt>,
    /// the position where the method was defined
    pub pos: TokenStream,
}

impl Method {
    /// creates a new method without any associated TokenStream
    ///
    /// # Arguments
    ///
    /// * `name` - the name of the method
    /// * `rettype` - the return type of the method
    /// * `args` - a list of function arguments
    pub fn new(name: String, rettype: Type, args: Vec<Param>) -> Self {
        Method {
            name,
            rettype,
            args,
            requires: Vec::new(),
            ensures: Vec::new(),
            stmts: None,
            pos: TokenStream::empty(),
        }
    }

    pub fn is_translate(&self) -> bool {
        self.name == "translate"
    }

    pub fn is_matchflags(&self) -> bool {
        self.name == "matchflags"
    }


    /// checks whether the method parameters match the given signature
    ///
    /// # Arguments
    ///
    /// * `sig`    - the signature of the method (just a string)
    /// * `param`  - the [Param] struct representing the method's parameter
    /// * `name`   - the expected name of the parameter (produces warning)
    /// * `ty`     - the expected type of the parameter (produces error)
    ///
    /// # Return Value
    ///
    /// The number of issues found with the parameter
    ///
    /// # Notes
    ///
    /// * The supplied signature string is not interpreted and is only used for printing
    ///
    pub fn check_param(sig: &str, param: &Param, name: &str, ty: Type) -> Issues {
        let mut res = Issues::ok();

        if param.ptype != ty {
            let msg = format!(
                "argument type mismatch. expected `{}` but was `{}`",
                ty, param.ptype
            );
            let hint = format!(
                "change this argument to type `{}` to match function signature `{}`",
                ty, sig
            );
            VrsError::new_err(param.pos.clone(), msg, Some(hint)).print();
            res.inc_err(1);
        }

        // we just raise a warning for the name at the moment
        if param.name != name {
            let msg = format!(
                "argument name mismatch. expected `{}` but was `{}`",
                name, param.name
            );
            let hint = format!(
                "change this argument name to `{}` to match function signature `{}`",
                name, sig
            );
            VrsError::new_warn(param.pos.clone(), msg, Some(hint)).print();
            res.inc_warn(1)
        }

        res
    }


    /// checks the `translate` method for compliance
    ///
    /// The `translate` method defines the translation part of the
    /// Unit's remapping functionality, and in particular produces
    /// a result if there is some mode of access that may result in
    /// a successful remapping
    ///
    /// # Arguments
    ///
    /// * `self`   - reference of the method
    /// * `st`     - the symbol table
    ///
    /// # Return Value
    ///
    /// The number of issues found with the method
    ///
    /// # Expecte Form
    ///
    ///   fn translate(va: addr) -> addr
    ///
    fn check_translate(&self, _st: &mut SymbolTable) -> Issues {
        assert_eq!(self.name, "translate");

        let mut res = Issues::ok();

        res = res + self.check_rettype(FN_SIG_TRANSLATE, Type::PhysicalAddress);
        res = res + self.check_argnum(FN_SIG_TRANSLATE, 1);

        if !self.args.is_empty() {
            res = res
                + Self::check_param(FN_SIG_TRANSLATE, &self.args[0], "va", Type::VirtualAddress);
        }

        res
    }

    /// checks the `matchflags` method for compliance
    ///
    /// The `matchflags` methods defines the permission part of the
    /// unit's remapping functionality, and in particular produces
    /// a boolean value whether the set permissions of match the
    /// flags
    ///
    /// # Arguments
    ///
    /// * `self`   - reference of the method
    /// * `st`     - the symbol table
    ///
    /// # Expected Form
    ///
    ///   fn matchflags(flgs: flags) -> bool
    ///
    fn check_matchflags(&self, _st: &mut SymbolTable) -> Issues {
        assert_eq!(self.name, "matchflags");

        let mut res = Issues::ok();

        res = res + self.check_rettype(FN_SIG_MATCHFLAGS, Type::Boolean);
        res = res + self.check_argnum(FN_SIG_MATCHFLAGS, 1);

        if !self.args.is_empty() {
            res = res + Self::check_param(FN_SIG_MATCHFLAGS, &self.args[0], "flgs", Type::Flags);
        }

        res
    }

    /// checks the `map` method for compliance
    ///
    /// The `map` methods defines the constraints on creating a new
    /// mapping (or a reconfiguration of) the unit's remapping functionality,
    /// and produces a boolean value whether the change in configuration
    /// succeeded
    ///
    /// # Arguments
    ///
    /// * `self`   - reference of the method
    /// * `st`     - the symbol table
    ///
    /// # Expected Form
    ///
    ///   fn map(va: addr, sz: size, flgs: flags, pa: addr) -> bool
    ///
    fn check_map(&self, _st: &mut SymbolTable) -> Issues {
        assert_eq!(self.name, "map");
        let mut res = Issues::ok();

        res = res + self.check_rettype(FN_SIG_MAP, Type::Boolean);
        res = res + self.check_argnum(FN_SIG_MAP, 4);

        if !self.args.is_empty() {
            res = res + Self::check_param(FN_SIG_MAP, &self.args[0], "va", Type::VirtualAddress);
        }
        if !self.args.len() >= 2 {
            res = res + Self::check_param(FN_SIG_MAP, &self.args[1], "sz", Type::Size);
        }
        if !self.args.len() >= 3 {
            res = res + Self::check_param(FN_SIG_MAP, &self.args[2], "flgs", Type::Flags);
        }
        if !self.args.len() >= 4 {
            res = res + Self::check_param(FN_SIG_MAP, &self.args[3], "pa", Type::PhysicalAddress);
        }

        res
    }

    /// checks the `unmap` method for compliance
    ///
    /// The `unmap` methods defines the constraints on removing an existing
    /// mapping (or a reconfiguration of) the unit's remapping functionality,
    /// and produces a boolean value whether the change in configuration
    /// succeeded
    ///
    /// # Arguments
    ///
    /// * `self`   - reference of the method
    /// * `st`     - the symbol table
    ///
    /// # Expected Form
    ///
    ///   fn unmap(va: addr, sz: size) -> bool
    ///
    fn check_unmap(&self, _st: &mut SymbolTable) -> Issues {
        assert_eq!(self.name, "unmap");
        let mut res = Issues::ok();

        res = res + self.check_rettype(FN_SIG_UNMAP, Type::Boolean);
        res = res + self.check_argnum(FN_SIG_UNMAP, 2);
        if !self.args.is_empty() {
            res = res + Self::check_param(FN_SIG_MAP, &self.args[0], "va", Type::Address);
        }
        if !self.args.len() >= 2 {
            res = res + Self::check_param(FN_SIG_MAP, &self.args[1], "sz", Type::Size);
        }
        res
    }

    /// checks the `protect` method for compliance
    ///
    /// The `protect` methods defines the constraints on changing the permissions
    /// of an existing mapping (or a reconfiguration of) the unit's remapping functionality,
    /// and produces a boolean value whether the change in configuration
    /// succeeded
    ///
    /// # Arguments
    ///
    /// * `self`   - reference of the method
    /// * `st`     - the symbol table
    ///
    /// # Expected Form
    ///
    ///   fn protect(va: addr, sz: size, flgs: flags) -> bool
    ///
    fn check_protect(&self, _st: &mut SymbolTable) -> Issues {
        assert_eq!(self.name, "protect");
        let mut res = Issues::ok();

        res = res + self.check_rettype(FN_SIG_PROTECT, Type::Boolean);

        res
    }


}


