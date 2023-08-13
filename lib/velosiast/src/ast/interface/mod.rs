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

// modules
mod actions;
mod fields;

// re-exports
pub use actions::VelosiAstInterfaceAction;
pub use fields::{
    VelosiAstInterfaceField, VelosiAstInterfaceMemoryField, VelosiAstInterfaceMmioField,
    VelosiAstInterfaceRegisterField,
};

use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::ops::Range;
use std::rc::Rc;

use velosiparser::{VelosiParseTreeInterface, VelosiParseTreeInterfaceDef, VelosiTokenStream};

use crate::ast::{
    types::{VelosiAstType, VelosiAstTypeInfo},
    VelosiAstBinOp, VelosiAstExpr, VelosiAstField, VelosiAstNode, VelosiAstParam,
};
use crate::ast::{VelosiAstBinOpExpr, VelosiAstNumLiteralExpr};
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

use super::expr::VelosiAstIdentLiteralExpr;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Definition
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Eq, Clone)]
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

        // check if we have double definitions in the parameters
        utils::check_param_double_definitions(&mut issues, &params);

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

    pub fn read_state_expr(&self, state_ref: &str, bits: Range<u64>) -> Option<Rc<VelosiAstExpr>> {
        let mut parts = state_ref.split('.');
        let (fieldname, _slicename) = match (parts.next(), parts.next(), parts.next()) {
            (Some("state"), Some(field), Some(slice)) => {
                (field.to_string(), Some(slice.to_string()))
            }
            (Some("state"), Some(field), None) => (field.to_string(), None),
            _ => return None,
        };

        let field_ref = format!("state.{}", fieldname);

        let mut state_accessors = Vec::new();

        // find the field that contains the state reference
        for field in &self.fields {
            for read_action in field.read_actions_as_ref() {
                match read_action.src.as_ref() {
                    VelosiAstExpr::IdentLiteral(ident) => {
                        let src_ident = ident.ident().as_ref();
                        if src_ident == state_ref || src_ident == &field_ref {
                            state_accessors.push((
                                read_action.src.clone(),
                                read_action.dst.clone(),
                                src_ident == state_ref,
                            ));
                        }
                    }
                    _ => panic!("TODO: source of read action not an ident literal"),
                }
            }
        }

        // ok now we have a list of (src, dst) tuples that contain (parts of) the state refrence
        if state_accessors.is_empty() {
            return None;
        }

        // obtain one state accessor, preferably one that is the full one
        let mut state_accessor = state_accessors.pop().unwrap();
        for acc in state_accessors.into_iter() {
            if acc.2 {
                state_accessor = acc
            }
        }

        assert!(matches!(
            state_accessor.1.as_ref(),
            VelosiAstExpr::IdentLiteral(_)
        ));

        if state_accessor.2 {
            // we have a precise match, then we can just return the dst
            Some(state_accessor.1)
        } else {
            // no precise match, this is mostly due to the action having a field <- field action,
            // here we need to find the the corresponding bit slice of the state and extract it
            // from the interface field

            let interface_field = match state_accessor.1.as_ref() {
                VelosiAstExpr::IdentLiteral(i) => self.fields_map.get(i.path().as_str()).unwrap(),
                _ => unreachable!(),
            };

            for slice in interface_field.layout_as_slice() {
                if slice.start == bits.start && slice.end == bits.end {
                    return Some(Rc::new(VelosiAstExpr::IdentLiteral(
                        VelosiAstIdentLiteralExpr::with_name(
                            slice.path_to_string(),
                            VelosiAstTypeInfo::Integer,
                        ),
                    )));
                }
            }

            // there was not an exact match of the bits, so we can construct something here
            // ((interface_field) >> bits.start) & (2^(bits.end - bits.start) - 1)
            debug_assert!(bits.end <= 64 && bits.start < bits.end);
            let mask = if bits.end == 64 && bits.start == 0 {
                0xffff_ffff_ffff_ffff
            } else {
                (1 << (bits.end - bits.start)) - 1
            };

            let shval = VelosiAstBinOpExpr::new(
                state_accessor.1,
                VelosiAstBinOp::RShift,
                Rc::new(VelosiAstExpr::NumLiteral(VelosiAstNumLiteralExpr::new(
                    bits.start,
                    Default::default(),
                ))),
                Default::default(),
            );

            let accessor = VelosiAstBinOpExpr::new(
                Rc::new(VelosiAstExpr::BinOp(shval)),
                VelosiAstBinOp::And,
                Rc::new(VelosiAstExpr::NumLiteral(VelosiAstNumLiteralExpr::new(
                    mask,
                    Default::default(),
                ))),
                Default::default(),
            );

            Some(Rc::new(VelosiAstExpr::BinOp(accessor)))
        }
    }
}

/// Implementation of [PartialEq] for [VelosiAstInterfaceDef]
impl PartialEq for VelosiAstInterfaceDef {
    fn eq(&self, other: &Self) -> bool {
        self.params == other.params
        // the params map is basically the same as the params
        && self.fields == other.fields
        // the fields_map is basically the same as the fields
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

/// Implementation of [Debug] for [VelosiAstInterfaceDef]
impl Debug for VelosiAstInterfaceDef {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

#[derive(PartialEq, Eq, Clone)]
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

    pub fn read_state_expr(&self, state_ref: &str, bits: Range<u64>) -> Option<Rc<VelosiAstExpr>> {
        match self {
            VelosiAstInterface::InterfaceDef(s) => s.read_state_expr(state_ref, bits),
            VelosiAstInterface::NoneInterface(_) => None,
        }
    }

    pub fn compare(&self, other: &Self) -> bool {
        match (self, other) {
            (VelosiAstInterface::InterfaceDef(s), VelosiAstInterface::InterfaceDef(o)) => {
                s.compare(o)
            }
            (VelosiAstInterface::NoneInterface(_), VelosiAstInterface::NoneInterface(_)) => true,
            _ => false,
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

/// Implementation of [Debug] for [VelosiAstInterface]
impl Debug for VelosiAstInterface {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
