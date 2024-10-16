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

// used standard library functionality

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used third-party crates
use indexmap::IndexMap;

// used parse tree definitions
use velosiparser::parsetree::{VelosiParseTreeUnitDef, VelosiParseTreeUnitNode};
use velosiparser::VelosiTokenStream;

use crate::ast::types::VelosiAstExternType;
// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{
    ast_result_return, ast_result_unwrap, unit_ignore_node, utils, AstResult, Symbol, SymbolTable,
    VelosiAstMethodProperty,
};

// used definitions of references AST nodes
use crate::ast::{
    VelosiAstConst, VelosiAstIdentifier, VelosiAstMethod, VelosiAstParam, VelosiAstTypeInfo,
    VelosiAstTypeProperty, VelosiAstUnit,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Operating System Spec
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Defines the variant of an enumeration
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiAstUnitOSSpec {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the parameters of the unit
    pub params: Vec<Rc<VelosiAstParam>>,
    /// constant defined within the osspec context
    pub consts: IndexMap<String, Rc<VelosiAstConst>>,
    /// enums defined on the unit
    pub methods: IndexMap<String, Rc<VelosiAstMethod>>,
    /// the extern types defined in this spec
    pub extern_types: IndexMap<String, Rc<VelosiAstExternType>>,
    /// the location of the enum definition
    pub loc: VelosiTokenStream,
}

impl VelosiAstUnitOSSpec {
    pub fn empty() -> Self {
        VelosiAstUnitOSSpec {
            ident: VelosiAstIdentifier::from("empty"),
            params: Vec::new(),
            consts: IndexMap::new(),
            methods: IndexMap::new(),
            extern_types: IndexMap::new(),
            loc: VelosiTokenStream::default(),
        }
    }

    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeUnitDef,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstUnit, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // create a new context in the symbol table
        st.create_context("unit".to_string());

        // adding special types
        let et = Rc::new(VelosiAstExternType::from("UnitType"));
        let _ = st.insert(et.into());

        // convert all the unit parameters
        let mut params = Vec::new();
        let mut address_param: Option<VelosiTokenStream> = None;
        for p in pt.params.into_iter() {
            let param = Rc::new(ast_result_unwrap!(
                VelosiAstParam::from_parse_tree(p, false, st),
                issues
            ));

            if param.ptype.is_addr() {
                if let Some(loc) = &address_param {
                    let msg = "Unit has multiple address parameters defined.";
                    let hint = "Remove this parameter, or change its type";
                    let loc_msg = "This is the previous address parameter";
                    let e = VelosiAstErrBuilder::err(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_related_location(loc_msg.to_string(), loc.clone())
                        .build();
                    issues.push(e);
                } else {
                    address_param = Some(param.loc.clone());
                }
            }

            // add the param to the symbol table, if it doesn't exist already
            if let Err(e) = st.insert(param.clone().into()) {
                issues.push(*e);
            } else {
                params.push(param);
            }
        }

        if let Some(_d) = pt.derived {
            unimplemented!("add warning about derived here!");
        }

        let mut methods = IndexMap::new();
        let mut consts = IndexMap::new();
        let mut extern_types = IndexMap::new();
        for node in pt.nodes.into_iter() {
            match node {
                VelosiParseTreeUnitNode::Const(c) => {
                    let c = Rc::new(ast_result_unwrap!(
                        VelosiAstConst::from_parse_tree(c, st),
                        issues
                    ));
                    if let Err(e) = st.insert(c.clone().into()) {
                        issues.push(*e);
                    } else {
                        consts.insert(c.ident_to_string(), c);
                    }
                }
                VelosiParseTreeUnitNode::InBitWidth(_, _) => {
                    unit_ignore_node!(
                        VelosiParseTreeUnitNode::InBitWidth,
                        node,
                        &mut issues,
                        "OSSpec"
                    )
                }
                VelosiParseTreeUnitNode::OutBitWidth(_, _) => {
                    unit_ignore_node!(
                        VelosiParseTreeUnitNode::OutBitWidth,
                        node,
                        &mut issues,
                        "OSSpec"
                    )
                }
                VelosiParseTreeUnitNode::Flags(_) => {
                    unimplemented!("handle me!");
                }
                VelosiParseTreeUnitNode::State(_) => {
                    unit_ignore_node!(VelosiParseTreeUnitNode::State, node, &mut issues, "OSSpec")
                }
                VelosiParseTreeUnitNode::Interface(_) => {
                    unit_ignore_node!(
                        VelosiParseTreeUnitNode::Interface,
                        node,
                        &mut issues,
                        "OSSpec"
                    )
                }
                VelosiParseTreeUnitNode::Method(method) => {
                    let m = Rc::new(ast_result_unwrap!(
                        VelosiAstMethod::from_parse_tree(method, st, true),
                        issues
                    ));

                    if m.is_abstract {
                        let msg = "OS specification does not support abstract methods";
                        let hint = "remove this method or make it non-abstract";
                        let err = VelosiAstErrBuilder::err(msg.to_string())
                            .add_hint(hint.to_string())
                            .add_location(m.loc.from_self_with_subrange(0..1))
                            .build();
                        issues.push(err);
                    }

                    if m.is_synth {
                        let msg = "OS specification does not support synth methods";
                        let hint = "remove this method or make it non-abstract";
                        let err = VelosiAstErrBuilder::err(msg.to_string())
                            .add_hint(hint.to_string())
                            .add_location(m.loc.from_self_with_subrange(0..1))
                            .build();
                        issues.push(err);
                    }

                    if let Err(e) = st.insert(m.clone().into()) {
                        issues.push(*e);
                    } else {
                        methods.insert(m.ident_to_string(), m);
                    }
                }
                VelosiParseTreeUnitNode::Map(_) => {
                    unit_ignore_node!(VelosiParseTreeUnitNode::Map, node, &mut issues, "OSSpec")
                }
                VelosiParseTreeUnitNode::EnumEntry(_) => {
                    unit_ignore_node!(
                        VelosiParseTreeUnitNode::EnumEntry,
                        node,
                        &mut issues,
                        "OSSpec"
                    )
                }
                VelosiParseTreeUnitNode::Type(t) => {
                    let t = Rc::new(ast_result_unwrap!(
                        VelosiAstExternType::from_parse_tree(t, st),
                        issues
                    ));

                    if t.properties.contains(&VelosiAstTypeProperty::Descriptor) {
                        for field in &t.fields {
                            let mut sym: Symbol = field.clone().into();
                            sym.name = Rc::new(format!("self.{}", field.ident()));
                            let _ = st.insert(sym);
                        }
                    }

                    // add the type to the symbol tbale
                    if let Err(e) = st.insert(t.clone().into()) {
                        issues.push(*e);
                    } else {
                        extern_types.insert(t.ident.to_string(), t);
                    }
                }
            }
        }

        if methods.contains_key("protect") {
            let msg = "Incomplete OS specification (missing function)";
            if !methods.contains_key("unmap") {
                let hint = "add the unmap() function specification, or remove all map/unmap/protect functions";
                let e = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(pt.loc.clone())
                    .build();
                issues.push(e);
            }

            if !(methods.contains_key("map")
                || methods
                    .values()
                    .fold(false, |acc, m| acc | m.ident().starts_with("map_")))
            {
                let hint = "add the map() function specification, or remove all map/unmap/protect functions";
                let e = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(pt.loc.clone())
                    .build();
                issues.push(e);
            }
        } else {
            let msg = "Incomplete OS specification (missing function)";
            if methods.contains_key("unmap") {
                let hint = "remove the unmap() function specification, or add all map/unmap/protect functions";
                let e = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(pt.loc.clone())
                    .build();
                issues.push(e);
            }

            if methods.contains_key("map")
                || methods
                    .values()
                    .fold(false, |acc, m| acc | m.ident().starts_with("map_"))
            {
                let hint = "remove the map() function specification, or add all map/unmap/protect functions";
                let e = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(pt.loc.clone())
                    .build();
                issues.push(e);
            }
        }

        let ident = VelosiAstIdentifier::from(pt.name);
        utils::check_camel_case(&mut issues, &ident);

        let res = VelosiAstUnitOSSpec {
            ident,
            consts,
            params,
            methods,
            extern_types,
            loc: pt.loc,
        };

        // and restore the context again.
        st.drop_context();

        ast_result_return!(VelosiAstUnit::OSSpec(Rc::new(res)), issues)
    }

    pub fn ident_to_string(&self) -> String {
        self.ident.as_str().to_string()
    }

    pub fn ident(&self) -> &Rc<String> {
        self.ident.ident()
    }

    /// checks whether the OSSpec contains definitions of those functions
    pub fn has_map_protect_unmap(&self) -> bool {
        self.methods.contains_key("protect")
            || self.methods.contains_key("unmap")
            || self.methods.contains_key("map")
            || self
                .methods
                .values()
                .fold(false, |acc, m| acc | m.ident().starts_with("map_"))
    }

    pub fn path_to_string(&self) -> String {
        self.ident.path.to_string()
    }

    pub fn path(&self) -> &Rc<String> {
        &self.ident.path
    }

    pub fn methods(&self) -> Box<dyn Iterator<Item = &Rc<VelosiAstMethod>> + '_> {
        Box::new(self.methods.values())
    }

    pub fn get_method(&self, name: &str) -> Option<&Rc<VelosiAstMethod>> {
        self.methods.get(name)
    }

    pub fn get_map_method(&self, dest_type: VelosiAstTypeProperty) -> Option<&Rc<VelosiAstMethod>> {
        for method in self.methods.values() {
            if method.ident.as_str().starts_with("map") {
                let pa = method.params_map.get("pa").unwrap();
                if let Some(tref) = pa.ptype.typeref() {
                    if let Some(ty) = self.extern_types.get(tref.as_str()) {
                        if ty.properties.contains(&dest_type) {
                            return Some(method);
                        }
                    }
                }
            }
        }
        None
    }

    pub fn get_extern_type_with_property(
        &self,
        dest_type: &VelosiAstTypeProperty,
    ) -> Option<&Rc<VelosiAstExternType>> {
        self.extern_types
            .values()
            .find(|&ty| ty.properties.contains(dest_type))
    }

    pub fn consts(&self) -> Box<dyn Iterator<Item = &Rc<VelosiAstConst>> + '_> {
        unimplemented!()
    }

    pub fn paddr_max(&self) -> u64 {
        unimplemented!()
    }

    pub fn vaddr_max(&self) -> u64 {
        unimplemented!()
    }

    pub fn params_as_slice(&self) -> &[Rc<VelosiAstParam>] {
        unimplemented!()
    }

    pub fn get_method_with_signature(
        &self,
        params: &[VelosiAstTypeInfo],
        rtype: &VelosiAstTypeInfo,
    ) -> Vec<Rc<VelosiAstMethod>> {
        self.methods
            .values()
            .filter(|m| m.matches_signature(params, rtype))
            .cloned()
            .collect()
    }

    fn get_methods_with_property_and_signature(
        &self,
        prop: &VelosiAstMethodProperty,
        params: &[VelosiAstTypeInfo],
        rtype: &VelosiAstTypeInfo,
    ) -> Vec<Rc<VelosiAstMethod>> {
        // try to get all methods with the alloc property first, the match the signature
        let methods: Vec<_> = self
            .get_method_with_property(prop)
            .iter()
            .filter(|m| m.matches_signature(params, rtype))
            .cloned()
            .collect();
        if !methods.is_empty() {
            return methods;
        }
        // look for other methods that may match the signature
        self.get_method_with_signature(params, rtype)
    }

    pub fn has_phys_alloc_fn(&self) -> bool {
        !self.get_phys_alloc_fn().is_empty()
    }

    pub fn get_phys_alloc_fn(&self) -> Vec<Rc<VelosiAstMethod>> {
        let rtype = VelosiAstTypeInfo::PhysAddr;
        let params = [VelosiAstTypeInfo::Size, VelosiAstTypeInfo::PhysAddr];

        self.get_methods_with_property_and_signature(
            &VelosiAstMethodProperty::MAlloc,
            &params,
            &rtype,
        )
    }

    pub fn get_virt_alloc_fn(&self) -> Vec<Rc<VelosiAstMethod>> {
        let rtype = VelosiAstTypeInfo::VirtAddr;
        let params = [VelosiAstTypeInfo::Size];

        self.get_methods_with_property_and_signature(
            &VelosiAstMethodProperty::MAlloc,
            &params,
            &rtype,
        )
    }

    pub fn get_phys_mem_free_fn(&self) -> Vec<Rc<VelosiAstMethod>> {
        let rtype = VelosiAstTypeInfo::Void;
        let params = [VelosiAstTypeInfo::PhysAddr, VelosiAstTypeInfo::Size];

        self.get_methods_with_property_and_signature(
            &VelosiAstMethodProperty::MFree,
            &params,
            &rtype,
        )
    }

    pub fn get_virt_mem_free_fn(&self) -> Vec<Rc<VelosiAstMethod>> {
        let rtype = VelosiAstTypeInfo::Void;
        let params = [VelosiAstTypeInfo::VirtAddr, VelosiAstTypeInfo::Size];

        self.get_methods_with_property_and_signature(
            &VelosiAstMethodProperty::MFree,
            &params,
            &rtype,
        )
    }

    pub fn get_method_with_property(
        &self,
        property: &VelosiAstMethodProperty,
    ) -> Vec<Rc<VelosiAstMethod>> {
        self.methods
            .values()
            .filter(|m| m.properties.contains(property))
            .cloned()
            .collect()
    }
}

/// Implementation of [Display] for [VelosiAstUnitOSSpec]
impl Display for VelosiAstUnitOSSpec {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "osspec {} (", self.ident)?;
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            Display::fmt(p, f)?;
        }
        writeln!(f, ") {{")?;

        // print the consts
        if !self.consts.is_empty() {
            writeln!(f)?;
            for c in self.consts.values() {
                let formatted = format!("{c}");
                for line in formatted.lines() {
                    writeln!(f, "  {line}")?;
                }
            }
        }
        // print the types
        if !self.extern_types.is_empty() {
            for ty in self.extern_types.values() {
                writeln!(f)?;
                let formatted = format!("{ty}");
                for line in formatted.lines() {
                    writeln!(f, "  {line}")?;
                }
            }
        }
        // print the methods
        if !self.methods.is_empty() {
            for method in self.methods.values() {
                let formatted = format!("{method}");
                writeln!(f)?;
                for line in formatted.lines() {
                    writeln!(f, "  {line}")?;
                }
            }
        }

        writeln!(f, "\n}}")
    }
}

/// Implementation of [Debug] for [VelosiAstUnitOSSpec]
impl Debug for VelosiAstUnitOSSpec {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
