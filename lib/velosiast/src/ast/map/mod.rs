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

//! # VelosiAst -- Static Map Definitions
//!
//! This module defines the static map AST nodes.

// Modules
mod element;
mod explicit;
mod listcomp;

// re-exports
pub use element::VelosiAstStaticMapElement;
pub use explicit::VelosiAstStaticMapExplicit;
pub use listcomp::VelosiAstStaticMapListComp;

// used standard library functionality
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeMap;
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::ast::VelosiAstUnit;
use crate::error::VelosiAstIssues;
use crate::{AstResult, SymbolTable, VelosiAstUnitProperty};

/// Represents a static map definition
#[derive(PartialEq, Eq, Clone)]
pub enum VelosiAstStaticMap {
    ListComp(VelosiAstStaticMapListComp),
    Explicit(VelosiAstStaticMapExplicit),
    None(VelosiTokenStream),
}

impl VelosiAstStaticMap {
    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeMap,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        use VelosiParseTreeMap::*;
        match pt {
            ListComp(pt) => VelosiAstStaticMapListComp::from_parse_tree(*pt, st),
            Explicit(pt) => VelosiAstStaticMapExplicit::from_parse_tree(*pt, st),
        }
    }

    pub fn name(&self) -> &str {
        "staticmap"
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiAstStaticMap::ListComp(s) => &s.loc,
            VelosiAstStaticMap::Explicit(s) => &s.loc,
            VelosiAstStaticMap::None(s) => s,
        }
    }

    pub fn inputsize(&self) -> u64 {
        match self {
            VelosiAstStaticMap::ListComp(s) => s.inputsize,
            VelosiAstStaticMap::Explicit(s) => s.inputsize,
            VelosiAstStaticMap::None(_) => 0,
        }
    }

    pub fn get_next_unit_idents(&self) -> Vec<&Rc<String>> {
        match self {
            VelosiAstStaticMap::ListComp(s) => s.get_next_unit_idents(),
            VelosiAstStaticMap::Explicit(s) => s.get_next_unit_idents(),
            VelosiAstStaticMap::None(_) => vec![],
        }
    }

    pub fn properties(&self) -> HashSet<VelosiAstUnitProperty> {
        match self {
            VelosiAstStaticMap::ListComp(s) => s.properties.clone(),
            VelosiAstStaticMap::Explicit(_s) => HashSet::new(),
            VelosiAstStaticMap::None(_) => HashSet::new(),
        }
    }

    // returns the size of the map in elements
    pub fn size(&self) -> usize {
        match self {
            VelosiAstStaticMap::ListComp(s) => s.size(),
            VelosiAstStaticMap::Explicit(s) => s.size(),
            VelosiAstStaticMap::None(_) => 0,
        }
    }

    pub fn in_memory_state_size(&self, child_units: &HashMap<Rc<String>, VelosiAstUnit>) -> u64 {
        match self {
            VelosiAstStaticMap::ListComp(s) => s.in_memory_state_size(child_units),
            VelosiAstStaticMap::Explicit(s) => s.in_memory_state_size(),
            VelosiAstStaticMap::None(_) => 0,
        }
    }

    pub fn has_memory_state(&self) -> bool {
        match self {
            VelosiAstStaticMap::ListComp(s) => s.has_memory_state(),
            VelosiAstStaticMap::Explicit(s) => s.has_memory_state(),
            VelosiAstStaticMap::None(_) => false,
        }
    }
}

/// Implementation of [Display] for [VelosiAstStaticMap]
impl Display for VelosiAstStaticMap {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiAstStaticMap::ListComp(s) => Display::fmt(s, f),
            VelosiAstStaticMap::Explicit(s) => Display::fmt(s, f),
            VelosiAstStaticMap::None(_) => write!(f, "NoneMap"),
        }
    }
}

/// Implementation of [Debug] for [VelosiAstStaticMap]
impl Debug for VelosiAstStaticMap {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

impl Default for VelosiAstStaticMap {
    fn default() -> Self {
        VelosiAstStaticMap::None(VelosiTokenStream::default())
    }
}
