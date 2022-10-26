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

use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use velosiparser::{
    VelosiParseTreeInterface, VelosiParseTreeInterfaceAction, VelosiParseTreeInterfaceDef,
    VelosiParseTreeInterfaceField, VelosiParseTreeInterfaceFieldMemory,
    VelosiParseTreeInterfaceFieldMmio, VelosiParseTreeInterfaceFieldNode,
    VelosiParseTreeInterfaceFieldRegister, VelosiTokenStream,
};

use crate::ast::VelosiAstIdentifier;
use crate::ast::{
    types::{VelosiAstType, VelosiAstTypeInfo},
    VelosiAstExpr, VelosiAstFieldSlice, VelosiAstNode, VelosiAstParam, VelosiAstStateField,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

use super::expr::VelosiAstIdentLiteralExpr;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Actions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents a state field
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstInterfaceAction {
    pub src: VelosiAstExpr,
    pub dst: VelosiAstExpr,
    pub loc: VelosiTokenStream,
}

impl VelosiAstInterfaceAction {
    pub fn new(src: VelosiAstExpr, dst: VelosiAstExpr, loc: VelosiTokenStream) -> Self {
        Self { src, dst, loc }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeInterfaceAction,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstInterfaceAction, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        let src = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(pt.src, st), issues);
        let dst = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(pt.dst, st), issues);

        // the destination must be an lvalue that can be assigned to.
        if !dst.is_lvalue() {
            let msg = format!("Destination of action `{}` is not an lvalue", dst);
            let hint = "Convert the expression to an lvalue";
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint.to_string())
                .add_location(dst.loc().clone())
                .build();
            issues.push(err);
        }

        ast_result_return!(VelosiAstInterfaceAction::new(src, dst, pt.loc), issues)
    }
}

impl Display for VelosiAstInterfaceAction {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{} -> {}", self.src, self.dst)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Nodes
////////////////////////////////////////////////////////////////////////////////////////////////////

struct FieldNodes {
    pub layout: Vec<Rc<VelosiAstFieldSlice>>,
    pub readactions: Vec<VelosiAstInterfaceAction>,
    pub writeactions: Vec<VelosiAstInterfaceAction>,
}

impl FieldNodes {
    pub fn is_empty(&self) -> bool {
        self.layout.is_empty() && self.readactions.is_empty() && self.writeactions.is_empty()
    }
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
            VelosiParseTreeInterfaceFieldNode::Layout(slices) => {
                if !nodes.layout.is_empty() && !slices.is_empty() {
                    let msg = "two layout blocks detected. Attempting to merge them.";
                    let hint = "consider merging with the previous block.";
                    let related = "this is the previous layout block.";
                    let err = VelosiAstErrBuilder::warn(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(slices[0].loc.clone())
                        .add_related_location(related.to_string(), nodes.layout[0].loc.clone())
                        .build();
                    issues.push(err);
                }

                for slice in slices {
                    let slice = Rc::new(ast_result_unwrap!(
                        VelosiAstFieldSlice::from_parse_tree(slice, ident.as_str(), size * 8),
                        issues
                    ));
                    st.insert(slice.clone().into())
                        .map_err(|e| issues.push(e))
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
    let sfn = format!("state.{}", ident);
    let sym = if let Some(sym) = st.lookup(&sfn) {
        if let VelosiAstNode::StateField(f) = &sym.ast_node {
            f
        } else {
            unreachable!("should only return a statefield node.")
        }
    } else {
        // no symbol, so there is no corresponding state field
        return ast_result_return!(nodes, issues);
    };

    match sym.as_ref() {
        VelosiAstStateField::Memory(sf) => {
            if is_memory {
                if nodes.is_empty() {
                    // all is empty, just take the things from the state field

                    let stexpr = VelosiAstExpr::IdentLiteral(VelosiAstIdentLiteralExpr::new(
                        vec![sf.ident.clone()],
                        VelosiAstTypeInfo::Integer,
                        VelosiTokenStream::default(),
                    ));
                    let ifexpr = VelosiAstExpr::IdentLiteral(VelosiAstIdentLiteralExpr::new(
                        vec![ident.clone()],
                        VelosiAstTypeInfo::Integer,
                        VelosiTokenStream::default(),
                    ));

                    nodes.layout = sf.layout.clone();
                    nodes.writeactions = vec![VelosiAstInterfaceAction::new(
                        ifexpr.clone(),
                        stexpr.clone(),
                        VelosiTokenStream::default(),
                    )];
                    nodes.readactions = vec![VelosiAstInterfaceAction::new(
                        stexpr,
                        ifexpr,
                        VelosiTokenStream::default(),
                    )];
                } else {
                    if nodes.layout.is_empty() {
                        let msg = "Interface field misses layout. Taking layout from state field with the same name.";
                        let related = "Layout taken from this state field";
                        let err = VelosiAstErrBuilder::warn(msg.to_string())
                            .add_location(loc.clone())
                            .add_related_location(related.to_string(), sf.loc.clone())
                            .build();
                        issues.push(err);

                        nodes.layout = sf.layout.clone();
                    }

                    if nodes.writeactions.is_empty() {}

                    if nodes.readactions.is_empty() {}
                }
            } else {
                // statefield with the same name exists, but is of a different type
                let msg =
                    "State and interface have a field with the same name, but of different kind.";
                let hint = "Change this field type to `memory`";
                let related = "This is the location of the state field definition";
                let err = VelosiAstErrBuilder::warn(msg.to_string())
                    .add_location(loc.clone())
                    .add_hint(hint.to_string())
                    .add_related_location(related.to_string(), sf.loc.clone())
                    .build();
                issues.push(err);
            }
        }
        VelosiAstStateField::Register(sf) => {
            if is_memory {
                // statefield with the same name exists, but is of a different type
                let msg =
                    "State and interface have a field with the same name, but of different kind.";
                let hint = "Change this field type to `reg` or `mmio`";
                let related = "This is the location of the state field definition";
                let err = VelosiAstErrBuilder::warn(msg.to_string())
                    .add_location(loc.clone())
                    .add_hint(hint.to_string())
                    .add_related_location(related.to_string(), sf.loc.clone())
                    .build();
                issues.push(err);
            } else {
            }
        }
    }

    ast_result_return!(nodes, issues)
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Memory Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstInterfaceMemoryField {
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
    /// Read actions
    pub readactions: Vec<VelosiAstInterfaceAction>,
    /// write actions
    pub writeactions: Vec<VelosiAstInterfaceAction>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstInterfaceMemoryField {
    pub fn new(
        ident: VelosiAstIdentifier,
        size: u64,
        base: VelosiAstIdentifier,
        offset: u64,
        layout: Vec<Rc<VelosiAstFieldSlice>>,
        readactions: Vec<VelosiAstInterfaceAction>,
        writeactions: Vec<VelosiAstInterfaceAction>,
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
            readactions,
            writeactions,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeInterfaceFieldMemory,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstInterfaceField, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convert the identifer and check for format
        let ident = VelosiAstIdentifier::from_parse_tree_with_prefix(pt.name, "interface");
        utils::check_snake_case(&mut issues, &ident);

        // check the size
        let size = utils::check_field_size(&mut issues, pt.size, &pt.loc);

        // convert the base region, check whether it exists
        let base = VelosiAstIdentifier::from(pt.base);
        utils::check_param_exists(&mut issues, st, &base);

        // create dummy memory field
        let n = Self::new(
            ident.clone(),
            size,
            base.clone(),
            pt.offset,
            vec![],
            vec![],
            vec![],
            pt.loc.clone(),
        );

        let s = Symbol::new(
            ident.name.clone(),
            VelosiAstType::new_int(),
            VelosiAstNode::InterfaceField(Rc::new(VelosiAstInterfaceField::Memory(n))),
        );

        st.insert(s).map_err(|e| issues.push(e)).ok();

        // the offset should be aligned to the size
        let offset = pt.offset;
        if offset % size != 0 {
            // warning
            let msg = "Offset is not a multiple of size size of the memory field";
            let hint = format!("Change offset to be a multiple of {}", size);
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(7..8))
                .build();
            issues.push(err);
        }

        // process the nodes
        let nodes = ast_result_unwrap!(
            handle_nodes(pt.nodes, st, &ident, &pt.loc, size, true),
            issues
        );

        // construct the ast node and return
        let res = Self::new(
            ident,
            size,
            base,
            offset,
            nodes.layout,
            nodes.readactions,
            nodes.writeactions,
            pt.loc,
        );

        // remove the symbol again.
        st.remove(res.ident.as_str());

        ast_result_return!(VelosiAstInterfaceField::Memory(res), issues)
    }

    pub fn ident_as_str(&self) -> &str {
        self.ident.name.as_str()
    }

    pub fn ident_as_rc_string(&self) -> Rc<String> {
        self.ident.name.clone()
    }

    pub fn ident_to_string(&self) -> String {
        self.ident.name.to_string()
    }
}

/// Implementation of [Display] for [VelosiAstInterfaceMemoryField]
impl Display for VelosiAstInterfaceMemoryField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "memory field")
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface MMIO Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstInterfaceMmioField {
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
    /// Read actions
    pub readactions: Vec<VelosiAstInterfaceAction>,
    /// write actions
    pub writeactions: Vec<VelosiAstInterfaceAction>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstInterfaceMmioField {
    pub fn new(
        ident: VelosiAstIdentifier,
        size: u64,
        base: VelosiAstIdentifier,
        offset: u64,
        layout: Vec<Rc<VelosiAstFieldSlice>>,
        readactions: Vec<VelosiAstInterfaceAction>,
        writeactions: Vec<VelosiAstInterfaceAction>,
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
            readactions,
            writeactions,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeInterfaceFieldMmio,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstInterfaceField, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convert the identifer and check for format
        let ident = VelosiAstIdentifier::from_parse_tree_with_prefix(pt.name, "interface");
        utils::check_snake_case(&mut issues, &ident);

        // check the size
        let size = utils::check_field_size(&mut issues, pt.size, &pt.loc);

        // convert the base region, check whether it exists
        let base = VelosiAstIdentifier::from(pt.base);
        utils::check_param_exists(&mut issues, st, &base);

        // create dummy memory field
        let n = Self::new(
            ident.clone(),
            size,
            base.clone(),
            pt.offset,
            vec![],
            vec![],
            vec![],
            pt.loc.clone(),
        );

        let s = Symbol::new(
            ident.name.clone(),
            VelosiAstType::new_int(),
            VelosiAstNode::InterfaceField(Rc::new(VelosiAstInterfaceField::Mmio(n))),
        );

        st.insert(s).map_err(|e| issues.push(e)).ok();

        // the offset should be aligned to the size
        let offset = pt.offset;
        if offset % size != 0 {
            // warning
            let msg = "Offset is not a multiple of size size of the memory field";
            let hint = format!("Change offset to be a multiple of {}", size);
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(7..8))
                .build();
            issues.push(err);
        }

        // process the nodes
        let nodes = ast_result_unwrap!(
            handle_nodes(pt.nodes, st, &ident, &pt.loc, size, false),
            issues
        );

        // construct the ast node and return
        let res = Self::new(
            ident,
            size,
            base,
            offset,
            nodes.layout,
            nodes.readactions,
            nodes.writeactions,
            pt.loc,
        );

        // remove the dummy symbol again.
        st.remove(res.ident.as_str());

        ast_result_return!(VelosiAstInterfaceField::Mmio(res), issues)
    }

    pub fn ident_as_str(&self) -> &str {
        self.ident.name.as_str()
    }

    pub fn ident_as_rc_string(&self) -> Rc<String> {
        self.ident.name.clone()
    }

    pub fn ident_to_string(&self) -> String {
        self.ident.name.to_string()
    }
}

/// Implementation of [Display] for [VelosiAstInterfaceRegisterField]
impl Display for VelosiAstInterfaceMmioField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "registers field")
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Register Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstInterfaceRegisterField {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the size of the field
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
        let size = utils::check_field_size(&mut issues, pt.size, &pt.loc);

        // create dummy memory field
        let n = Self::new(ident.clone(), size, vec![], vec![], vec![], pt.loc.clone());

        let s = Symbol::new(
            ident.name.clone(),
            VelosiAstType::new_int(),
            VelosiAstNode::InterfaceField(Rc::new(VelosiAstInterfaceField::Register(n))),
        );

        st.insert(s).map_err(|e| issues.push(e)).ok();

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
        st.remove(res.ident.as_str());

        ast_result_return!(VelosiAstInterfaceField::Register(res), issues)
    }

    pub fn ident_as_str(&self) -> &str {
        self.ident.name.as_str()
    }

    pub fn ident_as_rc_string(&self) -> Rc<String> {
        self.ident.name.clone()
    }

    pub fn ident_to_string(&self) -> String {
        self.ident.name.to_string()
    }
}

/// Implementation of [Display] for [VelosiAstInterfaceRegisterField]
impl Display for VelosiAstInterfaceRegisterField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "registers field")
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Field Wrapper
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiAstInterfaceField {
    Memory(VelosiAstInterfaceMemoryField),
    Register(VelosiAstInterfaceRegisterField),
    Mmio(VelosiAstInterfaceMmioField),
}

impl VelosiAstInterfaceField {
    pub fn ident_as_str(&self) -> &str {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.ident_as_str(),
            VelosiAstInterfaceField::Register(field) => field.ident_as_str(),
            VelosiAstInterfaceField::Mmio(field) => field.ident_as_str(),
        }
    }

    pub fn ident_as_rc_string(&self) -> Rc<String> {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.ident_as_rc_string(),
            VelosiAstInterfaceField::Register(field) => field.ident_as_rc_string(),
            VelosiAstInterfaceField::Mmio(field) => field.ident_as_rc_string(),
        }
    }

    pub fn ident_to_string(&self) -> String {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.ident_to_string(),
            VelosiAstInterfaceField::Register(field) => field.ident_to_string(),
            VelosiAstInterfaceField::Mmio(field) => field.ident_to_string(),
        }
    }

    pub fn size(&self) -> u64 {
        match self {
            VelosiAstInterfaceField::Memory(field) => field.size,
            VelosiAstInterfaceField::Register(field) => field.size,
            VelosiAstInterfaceField::Mmio(field) => field.size,
        }
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

/// Implementation fo the [From] trait for [Symbol] for conversion to symbol
impl From<Rc<VelosiAstInterfaceField>> for Symbol {
    fn from(f: Rc<VelosiAstInterfaceField>) -> Self {
        let n = VelosiAstNode::InterfaceField(f.clone());
        Symbol::new(f.ident_as_rc_string(), VelosiAstType::new_int(), n)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Definition
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstInterfaceDef {
    /// the parameters of the memory Interface
    pub params: Vec<Rc<VelosiAstParam>>,
    /// a map of the parameter Interfaces
    pub params_map: HashMap<String, Rc<VelosiAstParam>>,
    /// all the fields of this Interface
    pub fields: Vec<Rc<VelosiAstInterfaceField>>,
    /// a map of strings to fields
    pub fields_map: HashMap<String, Rc<VelosiAstInterfaceField>>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstInterfaceDef {
    pub fn new(
        params: Vec<Rc<VelosiAstParam>>,
        fields: Vec<Rc<VelosiAstInterfaceField>>,
        loc: VelosiTokenStream,
    ) -> Self {
        let mut params_map = HashMap::new();
        for p in &params {
            params_map.insert(p.ident_to_string(), p.clone());
        }
        let mut fields_map = HashMap::new();
        for f in &fields {
            fields_map.insert(f.ident_to_string(), f.clone());
        }
        VelosiAstInterfaceDef {
            params,
            params_map,
            fields,
            fields_map,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeInterfaceDef,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstInterface, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convert all the unit parameters
        let mut params = Vec::new();
        for p in pt.params.into_iter() {
            let param = Rc::new(ast_result_unwrap!(
                VelosiAstParam::from_parse_tree(p, false, st),
                issues
            ));

            // here we want to check if the parameter are also defined on the unit level
            // and whether the types match precisely
            if let Some(ps) = st.lookup(param.ident_as_str()) {
                if ps.typeinfo.typeinfo != param.ptype.typeinfo {
                    let msg = "Parameter type mismatch. Parameter must have the same type as the unit parameter";
                    let hint = format!("Change the type of this parameter to `{}`", ps.typeinfo);
                    let err = VelosiAstErrBuilder::err(msg.to_string())
                        .add_hint(hint)
                        .add_location(param.loc.clone())
                        .build();
                    issues.push(err);
                }

                if !matches!(ps.ast_node, VelosiAstNode::Param(_)) {
                    let msg = "Parameter was defined as a different kind of symbol.";
                    let hint = "Add this parameter to the unit parameters";
                    let err = VelosiAstErrBuilder::err(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(param.loc.clone())
                        .build();
                    issues.push(err);
                }
            } else {
                let err = VelosiAstErrUndef::new(param.ident_as_rc_string(), param.loc.clone());
                issues.push(err.into());
            }
            // we don't need to add those to the symbol table, as they are expected to match
            params.push(param);
        }

        let mut fields = Vec::new();
        for f in pt.fields.into_iter() {
            let field = Rc::new(ast_result_unwrap!(
                VelosiAstInterfaceField::from_parse_tree(f, st),
                issues
            ));

            st.insert(field.clone().into())
                .map_err(|e| issues.push(e))
                .ok();
            fields.push(field);
        }

        for f1 in fields.iter() {
            for f2 in fields.iter() {
                use VelosiAstInterfaceField::*;
                if let (Memory(m1), Memory(m2)) = (f1.as_ref(), f2.as_ref()) {
                    if (m1.ident == m2.ident)
                        || (m1.offset + m1.size < m2.offset)
                        || (m2.offset + m2.size < m1.offset)
                    {
                        continue;
                    }
                    let msg = "Memory field range overlap.";
                    let hint = format!("This field overlaps with field `{}`", m2.ident);
                    let related = "This is the field that overlaps with.";
                    let err = VelosiAstErrBuilder::err(msg.to_string())
                        .add_hint(hint)
                        .add_location(m1.loc.clone())
                        .add_related_location(related.to_string(), m2.loc.clone())
                        .build();
                    issues.push(err);
                }
            }
        }

        let res = Self::new(params, fields, pt.loc);
        ast_result_return!(VelosiAstInterface::InterfaceDef(res), issues)
    }
}

/// Implementation of [Display] for [VelosiAstInterfaceDef]
impl Display for VelosiAstInterfaceDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "InterfaceDef(...")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiAstInterface {
    InterfaceDef(VelosiAstInterfaceDef),
    NoneInterface(VelosiTokenStream),
}

impl VelosiAstInterface {
    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeInterface,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        use VelosiParseTreeInterface::*;
        match pt {
            InterfaceDef(pt) => VelosiAstInterfaceDef::from_parse_tree(pt, st),
            None(ts) => AstResult::Ok(VelosiAstInterface::NoneInterface(ts)),
        }
    }

    pub fn name(&self) -> &str {
        "Interface"
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiAstInterface::InterfaceDef(s) => &s.loc,
            VelosiAstInterface::NoneInterface(s) => s,
        }
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstInterface>> for Symbol {
    fn from(interface: Rc<VelosiAstInterface>) -> Self {
        let ti = VelosiAstType::from(interface.clone());
        let name = Rc::new(String::from("Interface"));
        Symbol::new(name, ti, VelosiAstNode::Interface(interface))
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstInterface>> for VelosiAstType {
    fn from(c: Rc<VelosiAstInterface>) -> Self {
        VelosiAstType::new(VelosiAstTypeInfo::Interface, c.loc().clone())
    }
}

/// Implementation of [Display] for [VelosiAstInterface]
impl Display for VelosiAstInterface {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiAstInterface::InterfaceDef(s) => Display::fmt(s, f),
            VelosiAstInterface::NoneInterface(_) => writeln!(f, "NoneInterface"),
        }
    }
}
