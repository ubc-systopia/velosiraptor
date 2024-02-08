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

//! # VelosiAst -- State Field Definition
//!
//! This module defines the state fields.

// modules
mod memory;
mod register;

// re-exports
pub use memory::VelosiAstStateMemoryField;
pub use register::VelosiAstStateRegisterField;

// used standard library functionality

use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeStateField;
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::VelosiAstIssues;
use crate::{AstResult, Symbol, SymbolTable};

// used definitions of references AST nodes

use crate::ast::{types::VelosiAstType, VelosiAstField, VelosiAstFieldSlice, VelosiAstNode};

////////////////////////////////////////////////////////////////////////////////////////////////////
// State Field Wrapper
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone)]
pub enum VelosiAstStateField {
    Memory(VelosiAstStateMemoryField),
    Register(VelosiAstStateRegisterField),
}

impl VelosiAstStateField {
    /// obtains a reference to the identifier
    pub fn ident(&self) -> &Rc<String> {
        match self {
            VelosiAstStateField::Memory(field) => field.ident(),
            VelosiAstStateField::Register(field) => field.ident(),
        }
    }

    /// obtains a copy of the identifer
    pub fn ident_to_string(&self) -> String {
        match self {
            VelosiAstStateField::Memory(field) => field.ident_to_string(),
            VelosiAstStateField::Register(field) => field.ident_to_string(),
        }
    }

    /// obtains a reference to the fully qualified path
    pub fn path(&self) -> &Rc<String> {
        match self {
            VelosiAstStateField::Memory(field) => field.path(),
            VelosiAstStateField::Register(field) => field.path(),
        }
    }

    /// obtains a copy of the fully qualified path
    pub fn path_to_string(&self) -> String {
        match self {
            VelosiAstStateField::Memory(field) => field.path_to_string(),
            VelosiAstStateField::Register(field) => field.path_to_string(),
        }
    }

    pub fn update_symbol_table(&self, st: &mut SymbolTable) {
        for slice in self.layout_as_slice() {
            st.update(slice.clone().into())
                .expect("updating symbol table\n");
        }
    }

    pub fn size(&self) -> u64 {
        match self {
            VelosiAstStateField::Memory(field) => field.size,
            VelosiAstStateField::Register(field) => field.size,
        }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiAstStateField::Memory(field) => &field.loc,
            VelosiAstStateField::Register(field) => &field.loc,
        }
    }

    pub fn layout_as_slice(&self) -> &[Rc<VelosiAstFieldSlice>] {
        match self {
            VelosiAstStateField::Memory(field) => field.layout.as_slice(),
            VelosiAstStateField::Register(field) => field.layout.as_slice(),
        }
    }

    pub fn bit_slice_idents(&self) -> HashSet<Rc<String>> {
        self.layout_as_slice()
            .iter()
            .map(|s| s.path().clone())
            .collect()
    }

    pub fn get_slice_mask_for_refs(&self, refs: &HashSet<Rc<String>>) -> u64 {
        match self {
            VelosiAstStateField::Memory(field) => field.get_slice_mask_for_refs(refs),
            VelosiAstStateField::Register(field) => field.get_slice_mask_for_refs(refs),
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeStateField,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        use VelosiParseTreeStateField::*;
        match pt {
            Memory(pt) => VelosiAstStateMemoryField::from_parse_tree(pt, st),
            Register(pt) => VelosiAstStateRegisterField::from_parse_tree(pt, st),
        }
    }

    pub fn compare(&self, other: &Self) -> bool {
        match (self, other) {
            (VelosiAstStateField::Memory(m1), VelosiAstStateField::Memory(m2)) => m1.compare(m2),
            (VelosiAstStateField::Register(r1), VelosiAstStateField::Register(r2)) => {
                r1.compare(r2)
            }
            _ => false,
        }
    }
}

/// Implementation of [Display] for [VelosiAstStateField]
impl Display for VelosiAstStateField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use VelosiAstStateField::*;
        match self {
            Memory(m) => Display::fmt(m, f),
            Register(r) => Display::fmt(r, f),
        }
    }
}

/// Implementation of [Debug] for [VelosiAstStateField]
impl Debug for VelosiAstStateField {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Implementation fo the [From] trait for [Symbol] for conversion to symbol
impl From<Rc<VelosiAstStateField>> for Symbol {
    fn from(f: Rc<VelosiAstStateField>) -> Self {
        let n = VelosiAstNode::StateField(f.clone());
        Symbol::new(f.path().clone(), VelosiAstType::new_int(), n)
    }
}
