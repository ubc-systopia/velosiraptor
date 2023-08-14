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

//! # VelosiAst - Register Interface Fields
//!
//! This modules defines the register interface fields.

// used standard library functionality
use std::any::Any;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeInterfaceFieldRegister;
use velosiparser::VelosiTokenStream;

// used crate functionality
use super::handle_nodes;
use crate::error::VelosiAstIssues;
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{
    VelosiAstField, VelosiAstFieldSlice, VelosiAstIdentifier, VelosiAstInterfaceAction,
    VelosiAstInterfaceField, VelosiAstNode, VelosiAstType,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Register Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Eq, Clone)]
pub struct VelosiAstInterfaceRegisterField {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the size of the field in bytes
    pub size: u64,
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

impl VelosiAstInterfaceRegisterField {
    pub fn new(
        ident: VelosiAstIdentifier,
        size: u64,
        layout: Vec<Rc<VelosiAstFieldSlice>>,
        readactions: Vec<VelosiAstInterfaceAction>,
        writeactions: Vec<VelosiAstInterfaceAction>,
        loc: VelosiTokenStream,
    ) -> Self {
        let mut layout_map = HashMap::new();
        for slice in &layout {
            layout_map.insert(slice.ident_to_string(), slice.clone());
            // XXX: stupd work around to enable lookup using the identifier
            let n = slice.ident().split('.').last().unwrap();
            layout_map.insert(n.to_string(), slice.clone());
        }

        Self {
            ident,
            size,
            layout,
            layout_map,
            readactions,
            writeactions,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeInterfaceFieldRegister,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstInterfaceField, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convert the identifer and check for format
        let ident = VelosiAstIdentifier::from_parse_tree_with_prefix(pt.name, "interface");
        utils::check_snake_case(&mut issues, &ident);

        // check the size
        let size_loc = pt.loc.from_self_with_subrange(3..4);
        let size = utils::check_field_size(&mut issues, pt.size, &size_loc);

        // create dummy memory field
        let n = Self::new(ident.clone(), size, vec![], vec![], vec![], pt.loc.clone());

        let s = Symbol::new(
            ident.path().clone(),
            VelosiAstType::new_int(),
            VelosiAstNode::InterfaceField(Rc::new(VelosiAstInterfaceField::Register(n))),
        );

        st.insert(s).map_err(|e| issues.push(*e)).ok();

        // process the nodes
        let nodes = ast_result_unwrap!(
            handle_nodes(pt.nodes, st, &ident, &pt.loc, size, false),
            issues
        );

        // construct the ast node and return
        let res = Self::new(
            ident,
            size,
            nodes.layout,
            nodes.readactions,
            nodes.writeactions,
            pt.loc,
        );

        // remove the dummy symbol again.
        st.remove(res.path());

        ast_result_return!(VelosiAstInterfaceField::Register(res), issues)
    }

    /// obtains a reference to the identifier
    pub fn ident(&self) -> &Rc<String> {
        self.ident.ident()
    }

    /// obtains a copy of the identifer
    pub fn ident_to_string(&self) -> String {
        self.ident.as_str().to_string()
    }

    /// obtains a reference to the fully qualified path
    pub fn path(&self) -> &Rc<String> {
        &self.ident.path
    }

    /// obtains a copy of the fully qualified path
    pub fn path_to_string(&self) -> String {
        self.ident.path.as_str().to_string()
    }

    pub fn mask(&self) -> u64 {
        let mut mask = 0;
        for slice in &self.layout {
            mask |= slice.mask();
        }
        mask
    }

    pub fn compare(&self, other: &Self) -> bool {
        self.ident == other.ident && self.size == other.size
        // TODO: compare actions
    }
}

impl VelosiAstField for VelosiAstInterfaceRegisterField {
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

/// Implementation of [PartialEq] for [VelosiAstInterfaceRegisterField]
impl PartialEq for VelosiAstInterfaceRegisterField {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident
        && self.size == other.size
        && self.layout == other.layout
        // layout map is basically the same as layout
        && self.readactions == other.readactions
        && self.writeactions == other.writeactions
    }
}

/// Implementation of [Display] for [VelosiAstInterfaceRegisterField]
impl Display for VelosiAstInterfaceRegisterField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "    reg {} [{}]", self.ident, self.size)?;

        if !self.layout.is_empty() || !self.readactions.is_empty() || !self.writeactions.is_empty()
        {
            writeln!(f, " {{")?;
        }

        if !self.layout.is_empty() {
            writeln!(f, "      Layout {{")?;
            for slice in &self.layout {
                write!(f, "        ")?;
                Display::fmt(slice, f)?;
                writeln!(f, ",")?;
            }
            writeln!(f, "      }},")?;
        }

        if !self.readactions.is_empty() {
            writeln!(f, "      ReadActions {{")?;
            for slice in &self.readactions {
                write!(f, "        ")?;
                Display::fmt(slice, f)?;
                writeln!(f, ";")?;
            }
            writeln!(f, "      }},")?;
        }

        if !self.writeactions.is_empty() {
            writeln!(f, "      WriteActions {{")?;
            for slice in &self.writeactions {
                write!(f, "        ")?;
                Display::fmt(slice, f)?;
                writeln!(f, ";")?;
            }
            writeln!(f, "      }},")?;
        }

        if !self.layout.is_empty() || !self.readactions.is_empty() || !self.writeactions.is_empty()
        {
            write!(f, "    }}")
        } else {
            Ok(())
        }
    }
}

/// Implementation of [Debug] for [VelosiAstInterfaceRegisterField]
impl Debug for VelosiAstInterfaceRegisterField {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
