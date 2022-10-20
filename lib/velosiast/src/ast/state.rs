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
    VelosiParseTreeFieldSlice, VelosiParseTreeState, VelosiParseTreeStateDef,
    VelosiParseTreeStateField, VelosiParseTreeStateFieldMemory, VelosiParseTreeStateFieldRegister,
    VelosiTokenStream,
};

use crate::ast::VelosiAstIdentifier;
use crate::ast::{
    types::{VelosiAstType, VelosiAstTypeInfo},
    VelosiAstNode, VelosiAstParam,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

////////////////////////////////////////////////////////////////////////////////////////////////////
// State Memory Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstFieldSlice {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,

    pub start: u64,
    pub end: u64,

    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstFieldSlice {
    pub fn new(ident: VelosiAstIdentifier, start: u64, end: u64, loc: VelosiTokenStream) -> Self {
        Self {
            ident,
            start,
            end,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeFieldSlice,
        field: &str,
        maxbits: u64,
    ) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convert the identifer and check for format
        let ident = VelosiAstIdentifier::from_parse_tree_with_prefix(pt.name, field);
        utils::check_snake_case(&mut issues, &ident);

        // check if we actually have a range
        if pt.start == pt.end {
            let msg = "Empty range.";
            let hint = "Increase the end of the range";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(pt.loc.from_self_with_subrange(0..3))
                .build();
            issues.push(err);
        }

        // check if the range makes sense
        if pt.start > pt.end {
            let msg = "Start of range is smaller than the end.";
            let hint = "Adjust the range bounds.";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(pt.loc.from_self_with_subrange(0..3))
                .build();
            issues.push(err);
        }

        if pt.end > maxbits {
            let msg = format!(
                "End of range exceeds maximum number of bits of field ({}).",
                maxbits
            );
            let hint = "Reduce the end of the range.";
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint.to_string())
                .add_location(pt.loc.from_self_with_subrange(2..3))
                .build();
            issues.push(err);
        }

        ast_result_return!(Self::new(ident, pt.start, pt.end, pt.loc), issues)
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

/// Implementation fo the [From] trait for [Symbol] for conversion to symbol
impl From<Rc<VelosiAstFieldSlice>> for Symbol {
    fn from(f: Rc<VelosiAstFieldSlice>) -> Self {
        let n = VelosiAstNode::StateFieldSlice(f.clone());
        Symbol::new(f.ident_as_rc_string(), VelosiAstType::new_int(), n)
    }
}

/// Implementation of [Display] for [VelosiAstFieldSlice]
impl Display for VelosiAstFieldSlice {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "{}..{} {}", self.start, self.end, self.ident.as_str())
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// State Memory Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Debug)]
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
        let size = utils::check_field_size(&mut issues, pt.size, &pt.loc);

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

        // convert the base region, check whether it exists
        let base = VelosiAstIdentifier::from(pt.base);
        utils::check_param_exists(&mut issues, st, &base);

        // convert the slices
        let mut layout = Vec::new();
        for s in pt.layout.into_iter() {
            let slice = Rc::new(ast_result_unwrap!(
                VelosiAstFieldSlice::from_parse_tree(s, ident.as_str(), size * 8),
                issues
            ));

            st.insert(slice.clone().into())
                .map_err(|e| issues.push(e))
                .ok();
            layout.push(slice);
        }

        // overlap check
        utils::slice_overlap_check(&mut issues, size * 8, layout.as_slice());

        // construct the ast node and return
        let res = Self::new(ident, size, base, offset, layout, pt.loc);
        ast_result_return!(VelosiAstStateField::Memory(res), issues)
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

/// Implementation of [Display] for [VelosiAstStateMemoryField]
impl Display for VelosiAstStateMemoryField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "memory field")
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// State Register Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstStateRegisterField {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the size of the field
    pub size: u64,
    /// layout of the field
    pub layout: Vec<Rc<VelosiAstFieldSlice>>,
    /// hashmap of the layout from slice name to slice
    pub layout_map: HashMap<String, Rc<VelosiAstFieldSlice>>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstStateRegisterField {
    pub fn new(
        ident: VelosiAstIdentifier,
        size: u64,
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
            layout,
            layout_map,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeStateFieldRegister,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstStateField, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convert the identifer and check for format
        let ident = VelosiAstIdentifier::from_parse_tree_with_prefix(pt.name, "state");
        utils::check_snake_case(&mut issues, &ident);

        // check the size
        let size = utils::check_field_size(&mut issues, pt.size, &pt.loc);

        // convert the slices
        let mut layout = Vec::new();
        for s in pt.layout.into_iter() {
            let slice = Rc::new(ast_result_unwrap!(
                VelosiAstFieldSlice::from_parse_tree(s, ident.as_str(), size * 8),
                issues
            ));

            st.insert(slice.clone().into())
                .map_err(|e| issues.push(e))
                .ok();
            layout.push(slice);
        }

        // overlap check
        utils::slice_overlap_check(&mut issues, size * 8, layout.as_slice());

        // construct the ast node and return
        let res = Self::new(ident, size, layout, pt.loc);
        ast_result_return!(VelosiAstStateField::Register(res), issues)
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

/// Implementation of [Display] for [VelosiAstStateRegisterField]
impl Display for VelosiAstStateRegisterField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "registers field")
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// State Field Wrapper
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiAstStateField {
    Memory(VelosiAstStateMemoryField),
    Register(VelosiAstStateRegisterField),
}

impl VelosiAstStateField {
    pub fn ident_as_str(&self) -> &str {
        match self {
            VelosiAstStateField::Memory(field) => field.ident_as_str(),
            VelosiAstStateField::Register(field) => field.ident_as_str(),
        }
    }

    pub fn ident_as_rc_string(&self) -> Rc<String> {
        match self {
            VelosiAstStateField::Memory(field) => field.ident_as_rc_string(),
            VelosiAstStateField::Register(field) => field.ident_as_rc_string(),
        }
    }

    pub fn ident_to_string(&self) -> String {
        match self {
            VelosiAstStateField::Memory(field) => field.ident_to_string(),
            VelosiAstStateField::Register(field) => field.ident_to_string(),
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

/// Implementation fo the [From] trait for [Symbol] for conversion to symbol
impl From<Rc<VelosiAstStateField>> for Symbol {
    fn from(f: Rc<VelosiAstStateField>) -> Self {
        let n = VelosiAstNode::StateField(f.clone());
        Symbol::new(f.ident_as_rc_string(), VelosiAstType::new_int(), n)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// State Definition
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstStateDef {
    /// the parameters of the memory state
    pub params: Vec<Rc<VelosiAstParam>>,
    /// a map of the parameter states
    pub params_map: HashMap<String, Rc<VelosiAstParam>>,
    /// all the fields of this state
    pub fields: Vec<Rc<VelosiAstStateField>>,
    /// a map of strings to fields
    pub fields_map: HashMap<String, Rc<VelosiAstStateField>>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstStateDef {
    pub fn new(
        params: Vec<Rc<VelosiAstParam>>,
        fields: Vec<Rc<VelosiAstStateField>>,
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
        VelosiAstStateDef {
            params,
            params_map,
            fields,
            fields_map,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeStateDef,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstState, VelosiAstIssues> {
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
                VelosiAstStateField::from_parse_tree(f, st),
                issues
            ));

            st.insert(field.clone().into())
                .map_err(|e| issues.push(e))
                .ok();
            fields.push(field);
        }

        for f1 in fields.iter() {
            for f2 in fields.iter() {
                use VelosiAstStateField::*;
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
        ast_result_return!(VelosiAstState::StateDef(res), issues)
    }
}

/// Implementation of [Display] for [VelosiAstStateDef]
impl Display for VelosiAstStateDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "StateDef(...")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiAstState {
    StateDef(VelosiAstStateDef),
    NoneState(VelosiTokenStream),
}

impl VelosiAstState {
    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeState,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        use VelosiParseTreeState::*;
        match pt {
            StateDef(pt) => VelosiAstStateDef::from_parse_tree(pt, st),
            None(ts) => AstResult::Ok(VelosiAstState::NoneState(ts)),
        }
    }

    pub fn name(&self) -> &str {
        "state"
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiAstState::StateDef(s) => &s.loc,
            VelosiAstState::NoneState(s) => s,
        }
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstState>> for Symbol {
    fn from(state: Rc<VelosiAstState>) -> Self {
        let ti = VelosiAstType::from(state.clone());
        let name = Rc::new(String::from("state"));
        Symbol::new(name, ti, VelosiAstNode::State(state))
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstState>> for VelosiAstType {
    fn from(c: Rc<VelosiAstState>) -> Self {
        VelosiAstType::new(VelosiAstTypeInfo::State, c.loc().clone())
    }
}

/// Implementation of [Display] for [VelosiAstState]
impl Display for VelosiAstState {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiAstState::StateDef(s) => Display::fmt(s, f),
            VelosiAstState::NoneState(_) => writeln!(f, "NoneState"),
        }
    }
}
