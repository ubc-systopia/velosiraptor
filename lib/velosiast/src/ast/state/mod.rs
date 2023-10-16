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
//! This module defines the State AST nodes of the language

// modules
mod fields;

// re-exports
pub use fields::{VelosiAstStateField, VelosiAstStateMemoryField, VelosiAstStateRegisterField};

use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::ops::Range;
use std::rc::Rc;

use velosiparser::parsetree::VelosiParseTreeState;
use velosiparser::VelosiTokenStream;

use crate::ast::{
    types::{VelosiAstType, VelosiAstTypeInfo},
    VelosiAstNode, VelosiAstParam,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

////////////////////////////////////////////////////////////////////////////////////////////////////
// State Definition
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Eq, Clone, Default)]
pub struct VelosiAstState {
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

impl VelosiAstState {
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
        VelosiAstState {
            params,
            params_map,
            fields,
            fields_map,
            loc,
        }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeState,
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

        // check if we have double definitions in the parameters
        utils::check_param_double_definitions(&mut issues, &params);

        let mut fields = Vec::new();
        for f in pt.fields.into_iter() {
            let field = Rc::new(ast_result_unwrap!(
                VelosiAstStateField::from_parse_tree(f, st),
                issues
            ));

            // TODO: move this logic to the RegisterField struct?

            let sym: Symbol = field.clone().into();
            // for register fields we need to check whether they are
            if let VelosiAstStateField::Register(reg) = field.as_ref() {
                if reg.private {
                    // this is a private register
                } else {
                    // this is a shared register, if it's not in the symbol table, add it to the
                    // root.
                    match st.lookup(&sym.name) {
                        Some(sym) => {
                            // we found it in the root context, now we can check the type
                            if let VelosiAstNode::StateField(sf) = &sym.ast_node {
                                if field.size() != sf.size() {
                                    // the size must be the same
                                    let msg = "Field size mismatch. Shared registes fields must have the same size.";
                                    let hint = format!("Make the field size  `{}`", sf.size());
                                    let related = "This is the previous definition of the field";
                                    let err = VelosiAstErrBuilder::err(msg.to_string())
                                        .add_hint(hint)
                                        .add_location(field.loc().clone())
                                        .add_related_location(related.to_string(), sf.loc().clone())
                                        .build();
                                    issues.push(err);
                                }

                                utils::check_layout_qauality(
                                    &mut issues,
                                    sf.layout_as_slice(),
                                    field.layout_as_slice(),
                                );
                            } else {
                                // error here
                            }
                        }
                        None => {
                            // nothing found in the symbol table, we can adde the symbol to the root
                            // context of the symbol table so it stays there in the compilation unit
                            st.insert_root(sym.clone()).ok();
                        }
                    }

                    // insert it to the current scope, in case there was a different layout, so
                    // other checks won't fail
                    st.insert_current(sym).map_err(|e| issues.push(*e)).ok();
                }
            } else {
                // this is a memory field, simply insert it into the symbol table.
                st.insert(sym).map_err(|e| issues.push(*e)).ok();
            }

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

        ast_result_return!(Self::new(params, fields, pt.loc), issues)
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

    pub fn get_field_range(&self, stateref: &str) -> Range<u64> {
        let mut parts = stateref.split('.');
        match (parts.next(), parts.next(), parts.next()) {
            (Some("state"), Some(field), Some(slice)) => {
                if let Some(f) = self.fields_map.get(field) {
                    for s in f.layout_as_slice() {
                        if s.ident().as_str() == slice {
                            return s.start..s.end;
                        }
                    }
                }
                0..0
            }
            (Some("state"), Some(field), None) => {
                if let Some(f) = self.fields_map.get(field) {
                    0..f.size()
                } else {
                    0..0
                }
            }
            _ => 0..0,
        }
    }

    pub fn get_registers(&self) -> Vec<Rc<VelosiAstStateField>> {
        self.fields
            .iter()
            .filter_map(|f| {
                if let VelosiAstStateField::Register(_r) = f.as_ref() {
                    Some(f.clone())
                } else {
                    None
                }
            })
            .collect()
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

    pub fn update_symbol_table(&self, st: &mut SymbolTable) {
        for f in &self.fields {
            f.update_symbol_table(st);
            st.update(f.clone().into())
                .expect("state already exists in symbolt able?");
        }
    }

    pub fn name(&self) -> &str {
        "state"
    }

    pub fn nfields(&self) -> usize {
        self.fields.len()
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        &self.loc
    }

    pub fn fields(&self) -> &[Rc<VelosiAstStateField>] {
        self.fields.as_slice()
    }

    pub fn has_memory(&self) -> bool {
        self.fields
            .iter()
            .any(|f| matches!(f.as_ref(), VelosiAstStateField::Memory(_)))
    }
}

impl PartialEq for VelosiAstState {
    fn eq(&self, other: &Self) -> bool {
        self.params == other.params && self.fields == other.fields
        // params_map and fields_map the same as params and fields
    }
}

/// Implementation of [Display] for [VelosiAstState]
impl Display for VelosiAstState {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "state(")?;
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            Display::fmt(p, f)?;
        }
        writeln!(f, ") {{")?;

        for field in self.fields.iter() {
            let formatted = format!("{}", field);
            for (i, line) in formatted.lines().enumerate() {
                if i > 0 {
                    writeln!(f)?;
                }
                write!(f, "  {line}")?;
            }
            writeln!(f, ",")?;
        }

        write!(f, "}}")
    }
}

/// Implementation of [Debug] for [VelosiAstState]
impl Debug for VelosiAstState {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
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
