// VelosiAst -- a Ast for the Velosiraptor Language
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

//! # VelosiAst -- Unit Definitions
//!
//! This module defines the Constant AST nodes of the langauge

// used standard library functionality

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used third-party crates
use indexmap::IndexMap;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeUnitDef;
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::VelosiAstIssues;
use crate::{AstResult, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{
    VelosiAstConst, VelosiAstIdentifier, VelosiAstMethod, VelosiAstParam, VelosiAstUnit,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Operating System Spec
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Defines the variant of an enumeration
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiAstUnitOSSpec {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the parameters of the unit
    pub params: Vec<Rc<VelosiAstParam>>,
    /// input addressing width
    pub inbitwidth: u64,
    /// output addressing width
    pub outbitwidth: u64,
    // enums defined on the unit
    pub methods: IndexMap<String, Rc<VelosiAstMethod>>,
    /// the location of the enum definition
    pub loc: VelosiTokenStream,
}

impl VelosiAstUnitOSSpec {
    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        _pt: VelosiParseTreeUnitDef,
        _st: &mut SymbolTable,
    ) -> AstResult<VelosiAstUnit, VelosiAstIssues> {
        unimplemented!()
    }

    pub fn ident_to_string(&self) -> String {
        unimplemented!()
    }

    pub fn ident(&self) -> &Rc<String> {
        unimplemented!()
    }

    pub fn path_to_string(&self) -> String {
        unimplemented!()
    }

    pub fn path(&self) -> &Rc<String> {
        unimplemented!()
    }

    pub fn methods(&self) -> Box<dyn Iterator<Item = &Rc<VelosiAstMethod>> + '_> {
        unimplemented!()
    }

    pub fn get_method(&self, _name: &str) -> Option<&Rc<VelosiAstMethod>> {
        unimplemented!()
    }

    pub fn consts(&self) -> Box<dyn Iterator<Item = &Rc<VelosiAstConst>> + '_> {
        unimplemented!()
    }

    pub fn paddr_max(&self) -> u64 {
        unimplemented!()
    }

    pub fn vaddr_max(&self) -> u64 {
        unimplemented!()
    }

    pub fn params_as_slice(&self) -> &[Rc<VelosiAstParam>] {
        unimplemented!()
    }
}

/// Implementation of [Display] for [VelosiAstUnitOSSpec]
impl Display for VelosiAstUnitOSSpec {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "os {} (", self.ident)?;
        // for (i, p) in self.params.iter().enumerate() {
        //     if i > 0 {
        //         write!(f, ", ")?;
        //     }
        //     Display::fmt(p, f)?;
        // }
        // write!(f, ")")?;
        // writeln!(f, " {{")?;

        // writeln!(f, "  inbitwidth = {};", self.inbitwidth)?;
        // writeln!(f, "  outbitwidth = {};\n", self.outbitwidth)?;

        // for (e, p) in &self.enums {
        //     write!(f, "  {e}(")?;
        //     for (i, p) in p.args.iter().enumerate() {
        //         if i > 0 {
        //             write!(f, ", ")?;
        //         }
        //         write!(f, "{p}")?;
        //     }
        //     writeln!(f, "  ),")?;
        // }

        write!(f, "\n}}")
    }
}

/// Implementation of [Debug] for [VelosiAstUnitOSSpec]
impl Debug for VelosiAstUnitOSSpec {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
