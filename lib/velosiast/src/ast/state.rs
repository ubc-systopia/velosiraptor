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

use velosiparser::{
    VelosiParseTreeFieldSlice, VelosiParseTreeState, VelosiParseTreeStateDef,
    VelosiParseTreeStateField, VelosiParseTreeStateFieldMemory, VelosiParseTreeStateFieldRegister,
    VelosiTokenStream,
};

use crate::ast::VelosiAstIdentifier;
use crate::ast::{
    types::{VelosiAstType, VelosiAstTypeInfo},
    VelosiAstField, VelosiAstFieldSlice, VelosiAstNode, VelosiAstParam,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

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
        let size_loc = pt.loc.from_self_with_subrange(7..8);
        let size = utils::check_field_size(&mut issues, pt.size, &size_loc);

        // the offset should be aligned to the size
        let offset = pt.offset;
        if offset % size != 0 {
            // warning
            let msg = "Offset is not a multiple of size size of the memory field";
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
        let layout = ast_result_unwrap!(handle_layout(pt.layout, st, &ident, size), issues);

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

    fn compare(&self, other: &Self) -> bool {
        self.ident == other.ident
            && self.size == other.size
            && self.base == other.base
            && self.offset == other.offset
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
        let size_loc = pt.loc.from_self_with_subrange(3..4);
        let size = utils::check_field_size(&mut issues, pt.size, &size_loc);

        // convert the slices
        let layout = ast_result_unwrap!(handle_layout(pt.layout, st, &ident, size), issues);

        // construct the ast node and return
        let res = Self::new(ident, size, layout, pt.loc);
        ast_result_return!(VelosiAstStateField::Register(res), issues)
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

    fn compare(&self, other: &Self) -> bool {
        self.ident == other.ident && self.size == other.size
    }
}

impl VelosiAstField for VelosiAstStateRegisterField {
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

/// Implementation of [Display] for [VelosiAstStateRegisterField]
impl Display for VelosiAstStateRegisterField {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "    reg {} [{}]", self.ident, self.size)?;
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

fn handle_layout(
    ptlayout: Vec<VelosiParseTreeFieldSlice>,
    st: &mut SymbolTable,
    ident: &VelosiAstIdentifier,
    size: u64,
) -> AstResult<Vec<Rc<VelosiAstFieldSlice>>, VelosiAstIssues> {
    let mut layout = Vec::new();
    let mut issues = VelosiAstIssues::new();

    // convert the slices
    if ptlayout.is_empty() {
        // if none, add syntactic sugar for a single slice that takes up the whole field
        let slice = Rc::new(VelosiAstFieldSlice::new(
            VelosiAstIdentifier::new(
                ident.path(),
                "_val".to_string(),
                VelosiTokenStream::default(),
            ),
            0,
            size * 8,
            VelosiTokenStream::default(),
        ));
        st.insert(slice.clone().into())
            .map_err(|e| issues.push(*e))
            .ok();
        layout.push(slice)
    } else {
        for s in ptlayout.into_iter() {
            let slice = Rc::new(ast_result_unwrap!(
                VelosiAstFieldSlice::from_parse_tree(s, ident.path(), size * 8),
                issues
            ));

            st.insert(slice.clone().into())
                .map_err(|e| issues.push(*e))
                .ok();
            layout.push(slice);
        }
    }

    // overlap check
    utils::slice_overlap_check(&mut issues, size * 8, layout.as_slice());

    ast_result_return!(layout, issues)
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

/// Implementation fo the [From] trait for [Symbol] for conversion to symbol
impl From<Rc<VelosiAstStateField>> for Symbol {
    fn from(f: Rc<VelosiAstStateField>) -> Self {
        let n = VelosiAstNode::StateField(f.clone());
        Symbol::new(f.path().clone(), VelosiAstType::new_int(), n)
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

            // TODO: check that we don't have any double-defined parameters!
        }

        let mut fields = Vec::new();
        for f in pt.fields.into_iter() {
            let field = Rc::new(ast_result_unwrap!(
                VelosiAstStateField::from_parse_tree(f, st),
                issues
            ));

            st.insert(field.clone().into())
                .map_err(|e| issues.push(*e))
                .ok();
            fields.push(field);
        }

        for f1 in fields.iter() {
            for f2 in fields.iter() {
                use VelosiAstStateField::*;
                if let (Memory(m1), Memory(m2)) = (f1.as_ref(), f2.as_ref()) {
                    if (m1.ident == m2.ident)
                        || (m1.offset + m1.size <= m2.offset)
                        || (m2.offset + m2.size <= m1.offset)
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

    /// obtains the state slice refs for the
    pub fn get_field_slice_refs(&self, refs: &HashSet<Rc<String>>) -> HashMap<Rc<String>, u64> {
        let mut hs = HashMap::new();
        for f in &self.fields {
            // if the entire field is part of that, add it
            let fid = f.path().clone();
            if refs.contains(&fid) {
                hs.insert(fid, 0xffff_ffff_ffff_ffff);
            } else {
                hs.insert(fid, f.get_slice_mask_for_refs(refs));
            }
        }
        hs
    }

    pub fn compare(&self, other: &Self) -> bool {
        if self.params.len() != other.params.len() {
            return false;
        }

        if self.fields.len() != other.fields.len() {
            return false;
        }

        for (i, p) in self.params.iter().enumerate() {
            if p != &other.params[i] {
                return false;
            }
        }

        for f1 in self.fields.iter() {
            if let Some(f2) = other.fields_map.get(f1.ident().as_str()) {
                if !f1.compare(f2) {
                    return false;
                }
            } else {
                return false;
            }
        }

        true
    }
}

/// Implementation of [Display] for [VelosiAstStateDef]
impl Display for VelosiAstStateDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "StateDef(")?;
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

    pub fn derive_from(&mut self, other: &Self) {
        use VelosiAstState::*;

        if matches!(other, NoneState(_)) {
            return;
        }

        if matches!(self, NoneState(_)) {
            *self = other.clone();
            return;
        }

        if let StateDef(s) = self {
            if let StateDef(o) = other {
                s.derive_from(o);
            }
        }
    }

    pub fn update_symbol_table(&self, st: &mut SymbolTable) {
        if matches!(self, VelosiAstState::NoneState(_)) {
            return;
        }

        for f in self.fields() {
            f.update_symbol_table(st);
            st.update(f.clone().into())
                .expect("state already exists in symbolt able?");
        }
    }

    pub fn name(&self) -> &str {
        "state"
    }

    pub fn is_none_state(&self) -> bool {
        matches!(self, VelosiAstState::NoneState(_))
    }

    pub fn nfields(&self) -> usize {
        use VelosiAstState::*;
        match self {
            StateDef(s) => s.fields.len(),
            NoneState(_) => 0,
        }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiAstState::StateDef(s) => &s.loc,
            VelosiAstState::NoneState(s) => s,
        }
    }

    pub fn fields(&self) -> &[Rc<VelosiAstStateField>] {
        match self {
            VelosiAstState::StateDef(s) => s.fields.as_slice(),
            VelosiAstState::NoneState(_s) => &[],
        }
    }

    pub fn get_field_slice_refs(&self, refs: &HashSet<Rc<String>>) -> HashMap<Rc<String>, u64> {
        match self {
            VelosiAstState::StateDef(s) => s.get_field_slice_refs(refs),
            VelosiAstState::NoneState(_s) => HashMap::new(),
        }
    }

    pub fn compare(&self, other: &Self) -> bool {
        match (self, other) {
            (VelosiAstState::StateDef(s), VelosiAstState::StateDef(o)) => s.compare(o),
            (VelosiAstState::NoneState(_), VelosiAstState::NoneState(_)) => true,
            _ => false,
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
