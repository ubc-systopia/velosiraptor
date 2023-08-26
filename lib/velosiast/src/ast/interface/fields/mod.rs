// Velosiraptor AST
//
//
// MIT License
//
// Copyright (c) 2021-2023 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiAst - Interface Fields
//!
//! This module contains the definition of the interface fields.

// modules
mod memory;
mod mmio;
mod register;

// re-exports
pub use memory::VelosiAstInterfaceMemoryField;
pub use mmio::VelosiAstInterfaceMmioField;
pub use register::VelosiAstInterfaceRegisterField;

// used standard library functionality
use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::{VelosiParseTreeInterfaceField, VelosiParseTreeInterfaceFieldNode};
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{
    VelosiAstExpr, VelosiAstField, VelosiAstFieldSlice, VelosiAstIdentLiteralExpr,
    VelosiAstIdentifier, VelosiAstInterfaceAction, VelosiAstNode, VelosiAstStateField,
    VelosiAstType, VelosiAstTypeInfo,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Field Wrapper
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone)]
pub enum VelosiAstInterfaceField {
    Memory(VelosiAstInterfaceMemoryField),
    Register(VelosiAstInterfaceRegisterField),
    Mmio(VelosiAstInterfaceMmioField),
}

impl VelosiAstInterfaceField {
    pub fn layout_as_slice(&self) -> &[Rc<VelosiAstFieldSlice>] {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.layout.as_slice(),
            VelosiAstInterfaceField::Register(field) => field.layout.as_slice(),
            VelosiAstInterfaceField::Mmio(field) => field.layout.as_slice(),
        }
    }

    pub fn slice(&self, ident: &str) -> Option<&VelosiAstFieldSlice> {
        match self {
            VelosiAstInterfaceField::Memory(field) => {
                field.layout_map.get(ident).map(|rc| rc.as_ref())
            }
            VelosiAstInterfaceField::Register(field) => {
                field.layout_map.get(ident).map(|rc| rc.as_ref())
            }
            VelosiAstInterfaceField::Mmio(field) => {
                field.layout_map.get(ident).map(|rc| rc.as_ref())
            }
        }
    }

    pub fn size(&self) -> u64 {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.size,
            VelosiAstInterfaceField::Register(field) => field.size,
            VelosiAstInterfaceField::Mmio(field) => field.size,
        }
    }

    pub fn nbits(&self) -> u64 {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.nbits(),
            VelosiAstInterfaceField::Register(field) => field.nbits(),
            VelosiAstInterfaceField::Mmio(field) => field.nbits(),
        }
    }

    pub fn mask(&self) -> u64 {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.mask(),
            VelosiAstInterfaceField::Register(field) => field.mask(),
            VelosiAstInterfaceField::Mmio(field) => field.mask(),
        }
    }

    pub fn update_symbol_table(&self, st: &mut SymbolTable) {
        for slice in self.layout_as_slice() {
            st.update(slice.clone().into())
                .expect("updating symbol table\n");
        }
    }

    pub fn write_actions_as_ref(&self) -> &[VelosiAstInterfaceAction] {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.writeactions.as_slice(),
            VelosiAstInterfaceField::Register(field) => field.writeactions.as_slice(),
            VelosiAstInterfaceField::Mmio(field) => field.writeactions.as_slice(),
        }
    }

    pub fn read_actions_as_ref(&self) -> &[VelosiAstInterfaceAction] {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.readactions.as_slice(),
            VelosiAstInterfaceField::Register(field) => field.readactions.as_slice(),
            VelosiAstInterfaceField::Mmio(field) => field.readactions.as_slice(),
        }
    }

    pub fn accessing_state(
        &self,
        state_syms: &HashSet<Rc<String>>,
        state_bits: &HashMap<Rc<String>, u64>,
        if_bits: &HashMap<Rc<String>, u64>,
    ) -> HashSet<Rc<String>> {
        let mut res = HashSet::new();
        for action in self.read_actions_as_ref() {
            res.extend(action.get_iface_refs_for_state_update(state_syms, state_bits, if_bits));
        }

        for action in self.write_actions_as_ref() {
            res.extend(action.get_iface_refs_for_state_update(state_syms, state_bits, if_bits));
        }
        res
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiAstInterfaceField::Memory(field) => &field.loc,
            VelosiAstInterfaceField::Register(field) => &field.loc,
            VelosiAstInterfaceField::Mmio(field) => &field.loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeInterfaceField,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        use VelosiParseTreeInterfaceField::*;
        match pt {
            Memory(pt) => VelosiAstInterfaceMemoryField::from_parse_tree(pt, st),
            Register(pt) => VelosiAstInterfaceRegisterField::from_parse_tree(pt, st),
            Mmio(pt) => VelosiAstInterfaceMmioField::from_parse_tree(pt, st),
        }
    }

    pub fn compare(&self, other: &Self) -> bool {
        match (self, other) {
            (VelosiAstInterfaceField::Memory(f1), VelosiAstInterfaceField::Memory(f2)) => {
                f1.compare(f2)
            }
            (VelosiAstInterfaceField::Register(f1), VelosiAstInterfaceField::Register(f2)) => {
                f1.compare(f2)
            }
            (VelosiAstInterfaceField::Mmio(f1), VelosiAstInterfaceField::Mmio(f2)) => {
                f1.compare(f2)
            }
            _ => false,
        }
    }
}

impl VelosiAstField for VelosiAstInterfaceField {
    /// obtains a reference to the identifier
    fn ident(&self) -> &Rc<String> {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.ident(),
            VelosiAstInterfaceField::Register(field) => field.ident(),
            VelosiAstInterfaceField::Mmio(field) => field.ident(),
        }
    }

    /// obtains a copy of the identifer
    fn ident_to_string(&self) -> String {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.ident_to_string(),
            VelosiAstInterfaceField::Register(field) => field.ident_to_string(),
            VelosiAstInterfaceField::Mmio(field) => field.ident_to_string(),
        }
    }

    /// obtains a reference to the fully qualified path
    fn path(&self) -> &Rc<String> {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.path(),
            VelosiAstInterfaceField::Register(field) => field.path(),
            VelosiAstInterfaceField::Mmio(field) => field.path(),
        }
    }

    /// obtains a copy of the fully qualified path
    fn path_to_string(&self) -> String {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.path_to_string(),
            VelosiAstInterfaceField::Register(field) => field.path_to_string(),
            VelosiAstInterfaceField::Mmio(field) => field.path_to_string(),
        }
    }

    /// obtains the layout of the field
    fn layout(&self) -> &[Rc<VelosiAstFieldSlice>] {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.layout.as_slice(),
            VelosiAstInterfaceField::Register(field) => field.layout.as_slice(),
            VelosiAstInterfaceField::Mmio(field) => field.layout.as_slice(),
        }
    }

    /// the size of the field in bits
    fn nbits(&self) -> u64 {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.nbits(),
            VelosiAstInterfaceField::Register(field) => field.nbits(),
            VelosiAstInterfaceField::Mmio(field) => field.nbits(),
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

/// Implementation of [Display] for [VelosiAstInterfaceField]
impl Display for VelosiAstInterfaceField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use VelosiAstInterfaceField::*;
        match self {
            Memory(m) => Display::fmt(m, f),
            Register(r) => Display::fmt(r, f),
            Mmio(m) => Display::fmt(m, f),
        }
    }
}

/// Implementation of [Debug] for [VelosiAstInterfaceField]
impl Debug for VelosiAstInterfaceField {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Implementation fo the [From] trait for [Symbol] for conversion to symbol
impl From<Rc<VelosiAstInterfaceField>> for Symbol {
    fn from(f: Rc<VelosiAstInterfaceField>) -> Self {
        let n = VelosiAstNode::InterfaceField(f.clone());
        Symbol::new(f.path().clone(), VelosiAstType::new_int(), n)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Nodes
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents the sorted and filtered list of interface field nodes
#[derive(Debug)]
struct FieldNodes {
    pub layout: Vec<Rc<VelosiAstFieldSlice>>,
    pub readactions: Vec<VelosiAstInterfaceAction>,
    pub writeactions: Vec<VelosiAstInterfaceAction>,
}

impl FieldNodes {
    // pub fn is_empty(&self) -> bool {
    //     self.layout.is_empty() && self.readactions.is_empty() && self.writeactions.is_empty()
    // }
}

fn handle_nodes(
    ptnodes: Vec<VelosiParseTreeInterfaceFieldNode>,
    st: &mut SymbolTable,
    ident: &VelosiAstIdentifier,
    loc: &VelosiTokenStream,
    size: u64,
    is_memory: bool,
) -> AstResult<FieldNodes, VelosiAstIssues> {
    let mut issues = VelosiAstIssues::new();

    let mut nodes = FieldNodes {
        layout: Vec::new(),
        readactions: Vec::new(),
        writeactions: Vec::new(),
    };

    for ptn in ptnodes {
        match ptn {
            VelosiParseTreeInterfaceFieldNode::Layout(layout) => {
                if !nodes.layout.is_empty() && !layout.is_empty() {
                    let msg = "two layout blocks detected. Attempting to merge them.";
                    let hint = "consider merging with the previous block.";
                    let related = "this is the previous layout block.";
                    let err = VelosiAstErrBuilder::warn(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(layout.loc.clone())
                        .add_related_location(related.to_string(), nodes.layout[0].loc.clone())
                        .build();
                    issues.push(err);
                }

                for slice in layout.slices {
                    let slice = Rc::new(ast_result_unwrap!(
                        VelosiAstFieldSlice::from_parse_tree(slice, ident.path(), size * 8),
                        issues
                    ));
                    st.insert(slice.clone().into())
                        .map_err(|e| issues.push(*e))
                        .ok();
                    nodes.layout.push(slice);
                }
            }
            VelosiParseTreeInterfaceFieldNode::ReadActions(actions) => {
                if !nodes.readactions.is_empty() && !actions.actions.is_empty() {
                    let msg = "two readaction blocks detected. Attempting to merge them.";
                    let hint = "consider merging with the previous block.";
                    let related = "this is the previous readaction block.";
                    let err = VelosiAstErrBuilder::warn(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(actions.loc.clone())
                        .add_related_location(related.to_string(), nodes.readactions[0].loc.clone())
                        .build();
                    issues.push(err);
                }

                for action in actions.actions {
                    let action = ast_result_unwrap!(
                        VelosiAstInterfaceAction::from_parse_tree(action, st),
                        issues
                    );
                    nodes.readactions.push(action);
                }
            }
            VelosiParseTreeInterfaceFieldNode::WriteActions(actions) => {
                if !nodes.writeactions.is_empty() && !actions.actions.is_empty() {
                    let msg = "two readaction blocks detected. Attempting to merge them.";
                    let hint = "consider merging with the previous block.";
                    let related = "this is the previous readaction block.";
                    let err = VelosiAstErrBuilder::warn(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(actions.loc.clone())
                        .add_related_location(
                            related.to_string(),
                            nodes.writeactions[0].loc.clone(),
                        )
                        .build();
                    issues.push(err);
                }

                for action in actions.actions {
                    let action = ast_result_unwrap!(
                        VelosiAstInterfaceAction::from_parse_tree(action, st),
                        issues
                    );
                    nodes.writeactions.push(action);
                }
            }
        }
    }

    // do an overlap check with the layout slices
    utils::slice_overlap_check(&mut issues, size * 8, nodes.layout.as_slice());

    utils::actions_conflict_check(&mut issues, nodes.readactions.as_slice());
    utils::actions_conflict_check(&mut issues, nodes.writeactions.as_slice());

    // if all nodes are emtpy, check if there exists a state piece with the same name.
    let sfn = format!("state.{}", ident.ident());
    let sym = if let Some(sym) = st.lookup(&sfn) {
        if let VelosiAstNode::StateField(f) = &sym.ast_node {
            f
        } else {
            unreachable!("should only return a statefield node.")
        }
    } else {
        // no symbol, so there is no corresponding state field
        if nodes.layout.is_empty() {
            // just add a single slice that takes up the whole field
            let slice = Rc::new(VelosiAstFieldSlice::new(
                VelosiAstIdentifier::with_prefix(
                    ident.path(),
                    "val".to_string(),
                    VelosiTokenStream::default(),
                ),
                0,
                size * 8,
                VelosiTokenStream::default(),
            ));
            st.insert(slice.clone().into())
                .map_err(|e| issues.push(*e))
                .ok();
            nodes.layout.push(slice);
        }
        return ast_result_return!(nodes, issues);
    };

    match (is_memory, sym.as_ref()) {
        (true, VelosiAstStateField::Memory(sf)) => {
            if nodes.layout.is_empty() {
                if sf.size == size {
                    // copy over the layout from the state field, replace state with interface
                    for slice in &sf.layout {
                        let mut ifslice = slice.as_ref().clone();
                        ifslice.ident.ident =
                            Rc::new(ifslice.ident.ident.replace("state", "interface"));
                        ifslice.ident.path =
                            Rc::new(ifslice.ident.path.replace("state", "interface"));
                        nodes.layout.push(Rc::new(ifslice));
                    }
                } else {
                    // size mismatch!
                    // statefield with the same name exists, but is of a different type
                    let msg = "State and interface have a field with the same name, but of differnet size.";
                    let hint = "Change this field size to match the state field size";
                    let related = "This is the location of the state field definition";
                    let err = VelosiAstErrBuilder::warn(msg.to_string())
                        .add_location(loc.clone())
                        .add_hint(hint.to_string())
                        .add_related_location(related.to_string(), sf.loc.clone())
                        .build();
                    issues.push(err);
                }
            }

            let stident = VelosiAstIdentifier::new(sf.path().to_string(), sf.loc.clone());

            let stexpr = Rc::new(VelosiAstExpr::IdentLiteral(VelosiAstIdentLiteralExpr::new(
                vec![stident],
                VelosiAstTypeInfo::Integer,
                VelosiTokenStream::default(),
            )));

            let sifdent =
                VelosiAstIdentifier::new(sf.path().replace("state", "interface"), sf.loc.clone());
            let ifexpr = Rc::new(VelosiAstExpr::IdentLiteral(VelosiAstIdentLiteralExpr::new(
                vec![sifdent],
                VelosiAstTypeInfo::Integer,
                VelosiTokenStream::default(),
            )));

            if nodes.writeactions.is_empty() {
                nodes.writeactions = vec![VelosiAstInterfaceAction::new(
                    ifexpr.clone(),
                    stexpr.clone(),
                    VelosiTokenStream::default(),
                )];
            }

            if nodes.readactions.is_empty() {
                nodes.readactions = vec![VelosiAstInterfaceAction::new(
                    stexpr,
                    ifexpr,
                    VelosiTokenStream::default(),
                )];
            }
        }
        (false, VelosiAstStateField::Memory(sf)) => {
            // statefield with the same name exists, but is of a different type
            let msg = "State and interface have a field with the same name, but of different kind.";
            let hint = "Change this field type to `memory`";
            let related = "This is the location of the state field definition";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_location(loc.clone())
                .add_hint(hint.to_string())
                .add_related_location(related.to_string(), sf.loc.clone())
                .build();
            issues.push(err);
        }

        (false, VelosiAstStateField::Register(sf)) => {
            if nodes.layout.is_empty() {
                if sf.size == size {
                    // copy over the layout from the state field, replace state with interface
                    for slice in &sf.layout {
                        let mut ifslice = slice.as_ref().clone();
                        ifslice.ident.ident =
                            Rc::new(ifslice.ident.ident.replace("state", "interface"));
                        ifslice.ident.path =
                            Rc::new(ifslice.ident.path.replace("state", "interface"));
                        nodes.layout.push(Rc::new(ifslice));
                    }
                } else {
                    // size mismatch!
                    // statefield with the same name exists, but is of a different type
                    let msg = "State and interface have a field with the same name, but of differnet size.";
                    let hint = "Change this field size to match the state field size";
                    let related = "This is the location of the state field definition";
                    let err = VelosiAstErrBuilder::warn(msg.to_string())
                        .add_location(loc.clone())
                        .add_hint(hint.to_string())
                        .add_related_location(related.to_string(), sf.loc.clone())
                        .build();
                    issues.push(err);
                }
            }

            let stident = VelosiAstIdentifier::new(sf.path().to_string(), sf.loc.clone());

            let stexpr = Rc::new(VelosiAstExpr::IdentLiteral(VelosiAstIdentLiteralExpr::new(
                vec![stident],
                VelosiAstTypeInfo::Integer,
                VelosiTokenStream::default(),
            )));

            let sifdent =
                VelosiAstIdentifier::new(sf.path().replace("state", "interface"), sf.loc.clone());
            let ifexpr = Rc::new(VelosiAstExpr::IdentLiteral(VelosiAstIdentLiteralExpr::new(
                vec![sifdent],
                VelosiAstTypeInfo::Integer,
                VelosiTokenStream::default(),
            )));

            if nodes.writeactions.is_empty() {
                nodes.writeactions = vec![VelosiAstInterfaceAction::new(
                    ifexpr.clone(),
                    stexpr.clone(),
                    VelosiTokenStream::default(),
                )];
            }

            if nodes.readactions.is_empty() {
                nodes.readactions = vec![VelosiAstInterfaceAction::new(
                    stexpr,
                    ifexpr,
                    VelosiTokenStream::default(),
                )];
            }
        }
        (true, VelosiAstStateField::Register(sf)) => {
            // statefield with the same name exists, but is of a different type
            let msg = "State and interface have a field with the same name, but of different kind.";
            let hint = "Change this field type to `reg` or `mmio`";
            let related = "This is the location of the state field definition";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_location(loc.clone())
                .add_hint(hint.to_string())
                .add_related_location(related.to_string(), sf.loc.clone())
                .build();
            issues.push(err);
        }
    }

    ast_result_return!(nodes, issues)
}
