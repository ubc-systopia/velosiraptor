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

//! # VelosiAst -- State Definitions
//!
//! This module defines the State AST nodes of the langauge

use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

use std::rc::Rc;

use velosiparser::parsetree::VelosiParseTreeStateFieldMemory;
use velosiparser::VelosiTokenStream;

use crate::ast::VelosiAstIdentifier;
use crate::ast::{VelosiAstField, VelosiAstFieldSlice, VelosiAstStateField};
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, SymbolTable};

////////////////////////////////////////////////////////////////////////////////////////////////////
// State Memory Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Eq, Clone)]
pub struct VelosiAstStateMemoryField {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the size of the field
    pub size: u64,
    /// base this field is part of
    pub base: VelosiAstIdentifier,
    /// offset of this field within the base
    pub offset: u64,
    /// layout of the field
    pub layout: Vec<Rc<VelosiAstFieldSlice>>,
    /// hashmap of the layout from slice name to slice
    pub layout_map: HashMap<String, Rc<VelosiAstFieldSlice>>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstStateMemoryField {
    pub fn new(
        ident: VelosiAstIdentifier,
        size: u64,
        base: VelosiAstIdentifier,
        offset: u64,
        layout: Vec<Rc<VelosiAstFieldSlice>>,
        loc: VelosiTokenStream,
    ) -> Self {
        let mut layout_map = HashMap::new();
        for slice in &layout {
            layout_map.insert(slice.ident_to_string(), slice.clone());
        }

        Self {
            ident,
            size,
            base,
            offset,
            layout,
            layout_map,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeStateFieldMemory,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstStateField, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convert the identifer and check for format
        let ident = VelosiAstIdentifier::from_parse_tree_with_prefix(pt.name, "state");
        utils::check_snake_case(&mut issues, &ident);

        // check the size
        let size_loc = pt.loc.from_self_with_subrange(7..8);
        let size = utils::check_field_size(&mut issues, pt.size, &size_loc);

        // the offset should be aligned to the size
        let offset = pt.offset;
        if offset % size != 0 {
            // warning
            let msg = "Offset is not a multiple of size of the memory field";
            let hint = format!("Change offset to be a multiple of {size}");
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(5..6))
                .build();
            issues.push(err);
        }

        // convert the base region, check whether it exists
        let base = VelosiAstIdentifier::from(pt.base);
        utils::check_param_exists(&mut issues, st, &base);

        // convert the slices
        let layout = ast_result_unwrap!(
            VelosiAstFieldSlice::from_parse_tree_many(pt.layout, st, &ident, size),
            issues
        );

        // construct the ast node and return
        let res = Self::new(ident, size, base, offset, layout, pt.loc);
        ast_result_return!(VelosiAstStateField::Memory(res), issues)
    }

    /// obtains a bitmask for the refrenced slices in the supplied refs
    pub fn get_slice_mask_for_refs(&self, refs: &HashSet<Rc<String>>) -> u64 {
        self.layout.iter().fold(0, |acc, slice| {
            if refs.contains(slice.path()) {
                acc | slice.mask()
            } else {
                acc
            }
        })
    }

    pub fn compare(&self, other: &Self) -> bool {
        self.ident == other.ident
            && self.size == other.size
            && self.base == other.base
            && self.offset == other.offset
    }
}

/// Implementation of [PartialEq] for [VelosiAstStateMemoryField]
impl PartialEq for VelosiAstStateMemoryField {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident
            && self.size == other.size
            && self.base == other.base
            && self.offset == other.offset
            && self.layout == other.layout
        // layout map same as layout
    }
}

/// Implementation of [Display] for [VelosiAstStateMemoryField]
impl Display for VelosiAstStateMemoryField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "    mem {} [{}, {}, {}]",
            self.ident, self.base, self.offset, self.size
        )?;
        if !self.layout.is_empty() {
            writeln!(f, " {{")?;
            for slice in &self.layout {
                write!(f, "      ")?;
                Display::fmt(slice, f)?;
                writeln!(f, ",")?;
            }
            write!(f, "    }}")
        } else {
            Ok(())
        }
    }
}

/// Implementation of [Debug] for [VelosiAstStateMemoryField]
impl Debug for VelosiAstStateMemoryField {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

impl VelosiAstField for VelosiAstStateMemoryField {
    /// obtains a reference to the identifier
    fn ident(&self) -> &Rc<String> {
        self.ident.ident()
    }

    /// obtains a copy of the identifer
    fn ident_to_string(&self) -> String {
        self.ident.as_str().to_string()
    }

    /// obtains a reference to the fully qualified path
    fn path(&self) -> &Rc<String> {
        &self.ident.path
    }

    /// obtains a copy of the fully qualified path
    fn path_to_string(&self) -> String {
        self.ident.path.as_str().to_string()
    }

    /// obtains the layout of the field
    fn layout(&self) -> &[Rc<VelosiAstFieldSlice>] {
        self.layout.as_slice()
    }

    /// the size of the field in bits
    fn nbits(&self) -> u64 {
        self.size * 8
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
