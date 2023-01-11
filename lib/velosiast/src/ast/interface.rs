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

use std::collections::{HashMap, HashSet};
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
    VelosiAstExpr, VelosiAstField, VelosiAstFieldSlice, VelosiAstNode, VelosiAstParam,
    VelosiAstStateField,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

use super::expr::VelosiAstIdentLiteralExpr;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Actions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Defines an action that is executed on the interface
///
/// An action defines a read access to the state or a write access to the state. The latter
/// basically triggers a state transition.
///
/// Currently an action is basically an assignment that assigns the destination the value of the
/// source. If the destination is a StateRef, then this src => dst
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstInterfaceAction {
    /// the source operand of the action
    pub src: VelosiAstExpr,
    /// the destination operand of the action (lvalue expression)
    pub dst: VelosiAstExpr,
    /// the location where the action was defined
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

        // the types must match
        if !dst.result_type().compatible(src.result_type()) {
            let msg = "type mismatch";
            let hint = format!(
                "Cannot assign value of type `{}` to `{}`",
                src.result_type(),
                dst.result_type()
            );
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(dst.loc().clone())
                .build();
            issues.push(err);
        }

        // we can only assign number types for now
        if !src.result_type().is_numeric() {
            let msg = "unsupported type";
            let hint = format!(
                "Expected a numeric or boolean type, but got `{}`",
                src.result_type(),
            );
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(src.loc().clone())
                .build();
            issues.push(err);
        }

        // TODO: check the bit overflow

        ast_result_return!(VelosiAstInterfaceAction::new(src, dst, pt.loc), issues)
    }

    /// handles state accesses with a state reference in the destination
    ///
    /// # Example
    ///
    ///  - `interface.field.slice -> state.field.slice;`
    ///  - `interface.field       -> state.field.slice;`
    ///  - `interface.field.slice -> state.field;`
    ///  - `interface.field       -> state.field;`
    ///  -  `1                    -> state.field.slice;
    ///  -  `1                    -> state.field;
    pub fn get_iface_refs_for_state_update(
        &self,
        state_syms: &HashSet<Rc<String>>,
        state_bits: &HashMap<Rc<String>, u64>,
        if_bits: &HashMap<Rc<String>, u64>,
    ) -> HashSet<Rc<String>> {
        // TODO: here we should build the transitive closure of the
        //       state references. As the state can be update by moving
        //       data from one state field to another.

        let mut dst_refs = HashSet::new();
        self.dst.get_state_references(&mut dst_refs);
        if dst_refs.is_empty() {
            // there were no stare references
            return dst_refs;
        }

        let mut src_refs = HashSet::new();
        self.src.get_interface_references(&mut src_refs);
        if src_refs.is_empty() {
            // there were no interface references
            return dst_refs;
        }

        // we should not have multiple state or interface references in an lvalue
        debug_assert!(dst_refs.len() == 1);
        debug_assert!(src_refs.len() == 1);

        let dst_ref = dst_refs.iter().next().unwrap();
        let dst_ref_parts = dst_ref.split('.').collect::<Vec<&str>>();

        debug_assert_eq!(dst_ref_parts[0], "state");

        let src_ref = src_refs.iter().next().unwrap();
        let src_ref_parts = src_ref.split('.').collect::<Vec<&str>>();

        debug_assert_eq!(src_ref_parts[0], "interface");

        match (src_ref_parts.len(), dst_ref_parts.len()) {
            //  - `interface.field.slice -> state.field.slice;`
            (3, 3) => {
                // one-to-one match, we simply take the interface reference here.
                if state_syms.contains(dst_ref) {
                    src_refs
                } else {
                    HashSet::new()
                }
            }
            //  - `interface.field       -> state.field.slice;`
            (2, 3) => {
                //HashSet::new()
                // somehow here we could filter out slices > number of bits...
                if state_syms.contains(dst_ref) {
                    src_refs
                } else {
                    HashSet::new()
                }
            }
            //  - `interface.field.slice -> state.field;`
            (3, 2) => {
                let bits = state_bits.get(dst_ref).unwrap();
                if *bits != 0 {
                    src_refs
                } else {
                    HashSet::new()
                }
            }
            //  - `interface.field       -> state.field;`
            (2, 2) => {
                // add the interface elements that actually match the used state elements.
                let mut res = HashSet::new();
                //res.insert(src_ref.clone());
                let bits = state_bits.get(dst_ref).unwrap();
                for (fld, b) in if_bits {
                    if bits & b != 0 {
                        res.insert(fld.clone());
                    } else {
                    }
                }
                res
            }
            _ => {
                panic!("unsupported state access: {} -> {}", self.src, self.dst);
            }
        }
    }
}

/// implementation of trait [Display] for [VelosiAstInterfaceAction]
impl Display for VelosiAstInterfaceAction {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{} -> {}", self.src, self.dst)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Nodes
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents the sorted and filtered list of interface field nodes
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
        let size = utils::check_field_size(&mut issues, pt.size, &pt.loc);

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
}

/// Implementation of [Display] for [VelosiAstInterfaceMemoryField]
impl Display for VelosiAstInterfaceMemoryField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "    mem {} [{}, {}, {}]",
            self.ident, self.base, self.offset, self.size
        )?;

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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface MMIO Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstInterfaceMmioField {
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

impl VelosiAstInterfaceMmioField {
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
            VelosiAstNode::InterfaceField(Rc::new(VelosiAstInterfaceField::Mmio(n))),
        );

        st.insert(s).map_err(|e| issues.push(*e)).ok();

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

        let mut layout_map = HashMap::new();
        for slice in &nodes.layout {
            layout_map.insert(slice.path_to_string(), slice.clone());
            // XXX: stupd work around to enable lookup using the identifier
            // let n = slice.ident().split('.').last().unwrap();
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

        // remove the dummy symbol again.
        st.remove(res.path());

        ast_result_return!(VelosiAstInterfaceField::Mmio(res), issues)
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
}

impl VelosiAstField for VelosiAstInterfaceMmioField {
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
}

/// Implementation of [Display] for [VelosiAstInterfaceRegisterField]
impl Display for VelosiAstInterfaceMmioField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "    mmio {} [{}, {}, {}]",
            self.ident, self.base, self.offset, self.size
        )?;

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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Register Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Debug)]
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
        let size = utils::check_field_size(&mut issues, pt.size, &pt.loc);

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
        Symbol::new(f.path().clone(), VelosiAstType::new_int(), n)
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
            fields_map.insert(f.path_to_string(), f.clone());
            // XXX: stupd work around to enable lookup using the identifier
            // let n = f.ident().split('.').last().unwrap();
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
            if let Some(ps) = st.lookup(param.path()) {
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
                let err = VelosiAstErrUndef::new(param.ident().clone(), param.loc.clone());
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
                .map_err(|e| issues.push(*e))
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

    pub fn derive_from(&mut self, other: &Self) {
        for p in &other.params {
            if !self.params_map.contains_key(p.ident().as_str()) {
                self.params.push(p.clone());
                self.params_map.insert(p.ident_to_string(), p.clone());
            } else {
                unimplemented!("TODO: handle merging of existing params (add type check here)!");
            }
        }

        for f in &other.fields {
            if !self.fields_map.contains_key(f.ident().as_str()) {
                self.fields.push(f.clone());
                self.fields_map.insert(f.ident_to_string(), f.clone());
            } else {
                unimplemented!("TODO: handle merging of existing fields (add type check here)!");
            }
        }
    }

    pub fn fields_accessing_state(
        &self,
        state_syms: &HashSet<Rc<String>>,
        state_bits: &HashMap<Rc<String>, u64>,
    ) -> HashSet<Rc<String>> {
        let mut if_bits = HashMap::new();
        for f in &self.fields {
            for l in f.layout() {
                if_bits.insert(l.path().clone(), l.mask());
            }
        }

        let mut hs = HashSet::new();
        for f in &self.fields {
            let fhs = f.accessing_state(state_syms, state_bits, &if_bits);
            hs.extend(fhs)
        }
        hs
    }
}

/// Implementation of [Display] for [VelosiAstInterfaceDef]
impl Display for VelosiAstInterfaceDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "InterfaceDef(")?;
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            Display::fmt(p, f)?;
        }
        writeln!(f, ") {{")?;

        for field in self.fields.iter() {
            Display::fmt(field, f)?;
            writeln!(f, ",")?;
        }

        write!(f, "  }}")
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

    pub fn is_none(&self) -> bool {
        matches!(self, VelosiAstInterface::NoneInterface(_))
    }

    pub fn derive_from(&mut self, other: &Self) {
        use VelosiAstInterface::*;

        if matches!(other, NoneInterface(_)) {
            return;
        }

        if matches!(self, NoneInterface(_)) {
            *self = other.clone();
            return;
        }

        if let InterfaceDef(s) = self {
            if let InterfaceDef(o) = other {
                s.derive_from(o);
            }
        }
    }

    pub fn update_symbol_table(&self, st: &mut SymbolTable) {
        if matches!(self, VelosiAstInterface::NoneInterface(_)) {
            return;
        }

        for f in self.fields() {
            f.update_symbol_table(st);
            st.update(f.clone().into())
                .expect("state already exists in symbolt able?");
        }
    }

    pub fn fields(&self) -> &[Rc<VelosiAstInterfaceField>] {
        match self {
            VelosiAstInterface::InterfaceDef(def) => def.fields.as_slice(),
            VelosiAstInterface::NoneInterface(_) => &[],
        }
    }

    pub fn field(&self, name: &str) -> Option<&VelosiAstInterfaceField> {
        match self {
            VelosiAstInterface::InterfaceDef(def) => def.fields_map.get(name).map(|rc| rc.as_ref()),
            VelosiAstInterface::NoneInterface(_) => None,
        }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiAstInterface::InterfaceDef(s) => &s.loc,
            VelosiAstInterface::NoneInterface(s) => s,
        }
    }

    // returns a list of all the fields with action that touch one of the state elements
    pub fn fields_accessing_state(
        &self,
        state_syms: &HashSet<Rc<String>>,
        state_bits: &HashMap<Rc<String>, u64>,
    ) -> HashSet<Rc<String>> {
        match self {
            VelosiAstInterface::InterfaceDef(s) => s.fields_accessing_state(state_syms, state_bits),
            VelosiAstInterface::NoneInterface(_s) => HashSet::new(),
        }
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstInterface>> for Symbol {
    fn from(interface: Rc<VelosiAstInterface>) -> Self {
        let ti = VelosiAstType::from(interface.clone());
        let name = Rc::new(String::from("interface"));
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
