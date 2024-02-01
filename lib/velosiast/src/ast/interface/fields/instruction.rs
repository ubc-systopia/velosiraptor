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

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeInterfaceFieldInstruction;
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
// Interface Register Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Eq, Clone)]
pub struct VelosiAstInterfaceInstructionField {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// Read actions
    pub readactions: Vec<VelosiAstInterfaceAction>,
    /// write actions
    pub writeactions: Vec<VelosiAstInterfaceAction>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstInterfaceInstructionField {
    pub fn new(
        ident: VelosiAstIdentifier,
        readactions: Vec<VelosiAstInterfaceAction>,
        writeactions: Vec<VelosiAstInterfaceAction>,
        loc: VelosiTokenStream,
    ) -> Self {
        Self {
            ident,
            readactions,
            writeactions,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeInterfaceFieldInstruction,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstInterfaceField, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convert the identifer and check for format
        let ident = VelosiAstIdentifier::from_parse_tree_with_prefix(pt.name, "interface");
        utils::check_snake_case(&mut issues, &ident);

        // create dummy memory field
        let n = Self::new(ident.clone(), vec![], vec![], pt.loc.clone());

        let s = Symbol::new(
            ident.path().clone(),
            VelosiAstType::new_int(),
            VelosiAstNode::InterfaceField(Rc::new(VelosiAstInterfaceField::Instruction(n))),
        );

        st.insert(s).map_err(|e| issues.push(*e)).ok();

        // process the nodes
        let nodes = ast_result_unwrap!(
            handle_nodes(pt.nodes, st, &ident, &pt.loc, 0, false),
            issues
        );

        if !nodes.layout.is_empty() {
            let msg = format!(
                "instruction `{}` has a layout description that will be ignored",
                ident.as_str()
            );
            let hint = String::from("remove the layout specification");
            let err = VelosiAstErrBuilder::warn(msg)
                .add_hint(hint)
                .add_location(pt.loc.clone())
                .build();
            issues.push(err);
        }

        // construct the ast node and return
        let res = Self::new(ident, nodes.readactions, nodes.writeactions, pt.loc);

        // remove the dummy symbol again.
        st.remove(res.path());

        ast_result_return!(VelosiAstInterfaceField::Instruction(res), issues)
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
        0
    }

    pub fn compare(&self, other: &Self) -> bool {
        self.ident == other.ident
        // TODO: compare actions
    }
}

impl VelosiAstField for VelosiAstInterfaceInstructionField {
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
        &[]
    }

    /// the size of the field in bits
    fn nbits(&self) -> u64 {
        0
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

/// Implementation of [PartialEq] for [VelosiAstInterfaceInstructionField]
impl PartialEq for VelosiAstInterfaceInstructionField {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident
        // layout map is basically the same as layout
        && self.readactions == other.readactions
        && self.writeactions == other.writeactions
    }
}

/// Implementation of [Display] for [VelosiAstInterfaceInstructionField]
impl Display for VelosiAstInterfaceInstructionField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "instr {}", self.ident)?;

        if !self.readactions.is_empty() || !self.writeactions.is_empty() {
            writeln!(f, " {{")?;
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

        if !self.readactions.is_empty() || !self.writeactions.is_empty() {
            write!(f, "}}")
        } else {
            Ok(())
        }
    }
}

/// Implementation of [Debug] for [VelosiAstInterfaceInstructionField]
impl Debug for VelosiAstInterfaceInstructionField {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
