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

/// the signature of the translate function
const FN_SIG_TRANSLATE: &str = "fn translate(va: addr) -> addr";
const FN_SIG_MATCHFLAGS: &str = "fn matchflags(flags: int) -> bool";
const FN_SIG_MAP: &str = "fn map(va: addr, sz: size, flgs: flags, pa: addr)";
const FN_SIG_UNMAP: &str = "fn unmap(va: addr, sz: size)";
const FN_SIG_PROTECT: &str = "fn protect(va: addr, sz: size, flgs: flags)";
//const FN_SIG_INIT: &str = "fn `";

/// Defines a Method inside a unit
///
/// A method defines certain functionality of the translation unit.
///
/// # Examples
///
///  - Translate(): a method that translates an address (required)
///  - get_size(): a method that extracts the
#[derive(PartialEq, Clone)]
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

    /// converts the [Method] into a [Symbol] for the symbol table
    ///
    /// # Arguments
    ///
    ///  * `self`  - reference to the method
    ///
    /// # Return Value
    ///
    /// Symbol representing the method
    ///
    /// # Notes
    ///
    /// The type of the symbol as used in expressions is the method's return value.
    ///
    pub fn to_symbol(&self) -> Symbol {
        Symbol::new(
            self.name.clone(),
            self.rettype,
            SymbolKind::Function,
            self.pos.clone(),
            AstNode::Method(self),
        )
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

    /// checks whether the method's return type match the given signature
    ///
    /// # Arguments
    ///
    /// * `self`  - reference of the method
    /// * `sig`   - the signature of the method (just a string)
    /// * `ty`    - the expected return type of the parameter (produces error)
    ///
    /// # Return Value
    ///
    /// The number of issues found with the return type
    ///
    fn check_rettype(&self, sig: &str, ty: Type) -> Issues {
        if self.rettype != ty {
            let msg = String::from("function signature mismatch: wrong return type");
            let hint = format!(
                "change return type to match expected function signature: `{}`",
                sig
            );
            let r = 5 + self.args.len() * 3;
            VrsError::new_err(self.pos.with_range(r..r + 1), msg, Some(hint)).print();
            Issues::err()
        } else {
            Issues::ok()
        }
    }

    /// checks whether the method's number of arguments matched the expected count
    ///
    /// # Arguments
    ///
    /// * `self`   - reference of the method
    /// * `sig`    - the signature of the method (just a string)
    /// * `nargs`  - the expected return type of the parameter (produces error)
    ///
    /// # Return Value
    ///
    /// The number of issues found with the arguments
    ///
    fn check_argnum(&self, sig: &str, nargs: usize) -> Issues {
        if self.args.len() != nargs {
            let msg = String::from("function signature mismatch: wrong number of arguments");
            let hint = format!(
                "change arguments to match expected function  signature: `{}`",
                sig
            );
            VrsError::new_err(
                self.pos.with_range(3..(6 + self.args.len() * 3)),
                msg,
                Some(hint),
            )
            .print();
            Issues::err()
        } else {
            Issues::ok()
        }
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

    /// returns a set of state references made by this method
    ///
    /// This includes references made by the statements of the method body,
    /// and the ensures and requires clauses by the methods
    ///
    /// # Arguments
    ///
    /// * `self`  -  reference of the method
    ///
    /// # Return Value
    ///
    /// Hash set of strings containing all state references
    ///
    pub fn get_state_references(&self) -> HashSet<String> {
        let mut v = HashSet::new();

        if let Some(stmts) = &self.stmts {
            v.extend(stmts.get_state_references());
        }

        v.extend(
            self.ensures
                .iter()
                .flat_map(|s| s.get_state_references())
                .collect::<Vec<String>>(),
        );
        v.extend(
            self.requires
                .iter()
                .flat_map(|s| s.get_state_references())
                .collect::<Vec<String>>(),
        );
        v
    }

    pub fn get_state_references_body(&self) -> HashSet<String> {
        let mut v = HashSet::new();

        if let Some(stmts) = &self.stmts {
            v.extend(stmts.get_state_references());
        }

        v
    }

    pub fn get_state_references_pre(&self) -> HashSet<String> {
        let mut v = HashSet::new();
        v.extend(
            self.requires
                .iter()
                .flat_map(|s| s.get_state_references())
                .collect::<Vec<String>>(),
        );
        v
    }
}

/// Implementation of the [fmt::Display] trait for [Method]
impl fmt::Display for Method {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "fn {}() -> {} {{", self.name, self.rettype)?;
        self.stmts.iter().fold(Ok(()), |result, s| {
            result.and_then(|_| writeln!(f, "  {}", s))
        })?;
        writeln!(f, "}}")
    }
}

/// Implementation of the [fmt::Debug] trait for [Method]
impl fmt::Debug for Method {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.pos.input_sourcepos().input_pos();
        writeln!(
            f,
            "{:03}:{:03} | fn {}() -> {} {{",
            line, column, self.name, self.rettype
        )?;
        self.stmts.iter().fold(Ok(()), |result, s| {
            result.and_then(|_| writeln!(f, "  {:?}", s))
        })?;
        writeln!(f, "}}")
    }
}

/// implementation of [AstNodeGeneric] for [Method]
impl<'a> AstNodeGeneric<'a> for Method {
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        let mut res = Issues::ok();

        // Check 1: Parameter Identifiers
        // --------------------------------------------------------------------------------------
        // Type:        Errors
        // Description: Check if all parameter identifiers are unique
        // Notes:       --
        // --------------------------------------------------------------------------------------
        let errors = utils::check_double_entries(&self.args);
        res.inc_err(errors);

        // Check 2: Types
        // --------------------------------------------------------------------------------------
        // Type:        Errors
        // Description: Check if all parameters have the right type
        // Notes:       --
        // --------------------------------------------------------------------------------------

        match self.name.as_str() {
            "translate" => {
                res = res + self.check_translate(st);
            }
            "matchflags" => {
                res = res + self.check_matchflags(st);
            }
            "map" => {
                res = res + self.check_map(st);
            }
            "unmap" => {
                res = res + self.check_unmap(st);
            }
            "protect" => {
                res = res + self.check_protect(st);
            }
            _ => {}
        }

        // create a new symbol table context
        st.create_context(self.name.clone());

        // adding the parameters
        for p in &self.args {
            if !st.insert(p.to_symbol()) {
                res.inc_err(1);
            }
        }

        // TODO: adding return value

        // Check 3: Ensures clauses
        // --------------------------------------------------------------------------------------
        // Type:        Errors
        // Description: Check if all ensures clauses are well-defined
        // Notes:       --
        // --------------------------------------------------------------------------------------

        for e in &self.ensures {
            res = res + e.check(st);
        }

        // Check 4: Requires clauses
        // --------------------------------------------------------------------------------------
        // Type:        Errors
        // Description: Check if all requres clauses are well-defined
        // Notes:       --
        // --------------------------------------------------------------------------------------

        for e in &self.requires {
            res = res + e.check(st);
        }

        // Check 5: Statements
        // --------------------------------------------------------------------------------------
        // Type:        Errors
        // Description: Check if all statements are well-defined
        // Notes:       --
        // --------------------------------------------------------------------------------------

        if let Some(stmts) = &self.stmts {
            res = res + stmts.check(st);
        }

        // Check 6: Return Paths
        // --------------------------------------------------------------------------------------
        // Type:        Errors
        // Description: Check if all branches have a well-defined return path
        // Notes:       --
        // --------------------------------------------------------------------------------------

        if let Some(stmts) = &self.stmts {
            res = res + stmts.check_return_types(self.rettype, st);
        }

        // Check 7: Identifier snake_case
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: Checks if the identifier has snake_case
        // Notes:       --
        // --------------------------------------------------------------------------------------

        res = res + utils::check_snake_case(&self.name, &self.pos);

        // restore the symbol table again
        st.drop_context();

        // return the number of issues found
        res
    }

    fn name(&self) -> &str {
        &self.name
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        &self.pos
    }

    fn rewrite(&'a mut self) {
        let mut preconditions = Vec::new();
        for e in self.requires.drain(..) {
            preconditions.extend(e.split_and());
        }
        self.requires = preconditions;
    }
}
