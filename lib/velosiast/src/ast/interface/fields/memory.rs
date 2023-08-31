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

//! # VelosiAst - Memory Interface Fields
//!
//! This modules defines the memory interface fields.

// used standard library functionality
use std::any::Any;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeInterfaceFieldMemory;
use velosiparser::VelosiTokenStream;

// used crate functionality
use super::handle_nodes;
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{
    VelosiAstField, VelosiAstFieldSlice, VelosiAstIdentifier, VelosiAstInterfaceAction,
    VelosiAstInterfaceField, VelosiAstNode, VelosiAstType,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Memory Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Eq, Clone)]
pub struct VelosiAstInterfaceMemoryField {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the size of the field in bytes
    pub size: u64,
    /// base this field is part of
    pub base: VelosiAstIdentifier,
    /// offset of this field within the base
    pub offset: u64,
    /// layout of the field
    pub layout: Vec<Rc<VelosiAstFieldSlice>>,
    /// hashmap of the layout from slice name to slice
    pub layout_map: HashMap<String, Rc<VelosiAstFieldSlice>>,
    /// Read actions
    pub readactions: Vec<VelosiAstInterfaceAction>,
    /// write actions
    pub writeactions: Vec<VelosiAstInterfaceAction>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstInterfaceMemoryField {
    pub fn from_parse_tree(
        pt: VelosiParseTreeInterfaceFieldMemory,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstInterfaceField, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convert the identifer and check for format
        let ident = VelosiAstIdentifier::from_parse_tree_with_prefix(pt.name, "interface");
        utils::check_snake_case(&mut issues, &ident);

        // check the size
        let size_loc = pt.loc.from_self_with_subrange(7..8);
        let size = utils::check_field_size(&mut issues, pt.size, &size_loc);

        // convert the base region, check whether it exists
        let base = VelosiAstIdentifier::from(pt.base);
        utils::check_param_exists(&mut issues, st, &base);

        // create dummy memory field
        let n = Self {
            ident: ident.clone(),
            size,
            base: base.clone(),
            offset: pt.offset,
            layout: vec![],
            layout_map: HashMap::new(),
            readactions: vec![],
            writeactions: vec![],
            loc: pt.loc.clone(),
        };

        let s = Symbol::new(
            ident.path().clone(),
            VelosiAstType::new_int(),
            VelosiAstNode::InterfaceField(Rc::new(VelosiAstInterfaceField::Memory(n))),
        );

        st.insert(s).map_err(|e| issues.push(*e)).ok();

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

        // process the nodes
        let nodes = ast_result_unwrap!(
            handle_nodes(pt.nodes, st, &ident, &pt.loc, size, true),
            issues
        );

        let mut layout_map = HashMap::new();
        for slice in &nodes.layout {
            layout_map.insert(slice.path_to_string(), slice.clone());
            // XXX: stupd work around to enable lookup using the identifier
            // let n = slice.ident().split(IDENT_PATH_SEP).last().unwrap();
            layout_map.insert(slice.ident_to_string(), slice.clone());
        }

        // construct the ast node and return
        let res = Self {
            ident,
            size,
            base,
            offset,
            layout: nodes.layout,
            layout_map,
            readactions: nodes.readactions,
            writeactions: nodes.writeactions,
            loc: pt.loc,
        };

        // remove the symbol again.
        st.remove(res.path());

        ast_result_return!(VelosiAstInterfaceField::Memory(res), issues)
    }

    pub fn mask(&self) -> u64 {
        let mut mask = 0;
        for slice in &self.layout {
            mask |= slice.mask();
        }
        mask
    }

    pub fn compare(&self, other: &Self) -> bool {
        self.ident == other.ident
            && self.size == other.size
            && self.base == other.base
            && self.offset == other.offset
        // TODO: compare actions
    }
}

impl VelosiAstField for VelosiAstInterfaceMemoryField {
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

/// Implementation of [PartialEq] for [VelosiAstInterfaceMmioField]
impl PartialEq for VelosiAstInterfaceMemoryField {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident
        && self.size == other.size
        && self.base == other.base
        && self.offset == other.offset
        && self.layout == other.layout
        // layout map is basically the same as layout
        && self.readactions == other.readactions
        && self.writeactions == other.writeactions
    }
}

/// Implementation of [Display] for [VelosiAstInterfaceMemoryField]
impl Display for VelosiAstInterfaceMemoryField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "mem {} [{}, {}, {}]",
            self.ident, self.base, self.offset, self.size
        )?;

        if !self.layout.is_empty() || !self.readactions.is_empty() || !self.writeactions.is_empty()
        {
            writeln!(f, " {{")?;
        }

        if !self.layout.is_empty() {
            writeln!(f, "  Layout {{")?;
            for slice in &self.layout {
                let formatted = format!("{slice}");
                for (i, line) in formatted.lines().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "    {line}")?;
                }
                writeln!(f, ",")?;
            }
            writeln!(f, "  }},")?;
        }

        if !self.readactions.is_empty() {
            writeln!(f, "  ReadActions {{")?;
            for action in &self.readactions {
                let formatted = format!("{action}");
                for (i, line) in formatted.lines().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "    {line}")?;
                }
                writeln!(f, ";")?;
            }
            writeln!(f, "  }},")?;
        }

        if !self.writeactions.is_empty() {
            writeln!(f, "  WriteActions {{")?;
            for action in &self.writeactions {
                let formatted = format!("{action}");
                for (i, line) in formatted.lines().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "    {line}")?;
                }
                writeln!(f, ";")?;
            }
            writeln!(f, "  }},")?;
        }

        if !self.layout.is_empty() || !self.readactions.is_empty() || !self.writeactions.is_empty()
        {
            write!(f, "}}")
        } else {
            Ok(())
        }
    }
}

/// Implementation of [Debug] for [VelosiAstInterfaceMemoryField]
impl Debug for VelosiAstInterfaceMemoryField {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
