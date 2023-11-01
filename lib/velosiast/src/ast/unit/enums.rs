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
//! This module defines the Constant AST nodes of the language

// used standard library functionality
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used third-party crates
use indexmap::IndexMap;

// used parse tree definitions
use velosiparser::parsetree::{VelosiParseTreeUnitDef, VelosiParseTreeUnitNode};
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::{
    VelosiAstErrBuilder, VelosiAstErrDoubleDef, VelosiAstErrUndef, VelosiAstIssues,
};
use crate::{
    ast_result_return, ast_result_unwrap, unit_ignore_node, utils, AstResult, SymbolTable,
};

// used definitions of references AST nodes
use crate::ast::{
    VelosiAstExpr, VelosiAstIdentifier, VelosiAstMethod, VelosiAstNode, VelosiAstParam,
    VelosiAstTypeInfo, VelosiAstUnit,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Enum Variant
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Defines the variant of an enumeration
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiAstUnitEnumVariant {
    /// identifier of the unit
    pub ident: VelosiAstIdentifier,
    /// arguments for the initialization of the variant
    pub args: Vec<VelosiAstIdentifier>,
    /// vector of expressions forming the CNF of the differentiator expression for this variant
    pub differentiator: Vec<Rc<VelosiAstExpr>>,
    /// whether the variant has some memory state
    pub has_memory_state: bool,
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Enum Unit
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone)]
pub struct VelosiAstUnitEnum {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the parameters of the unit
    pub params: Vec<Rc<VelosiAstParam>>,
    /// input addressing width
    pub inbitwidth: u64,
    /// output addressing width
    pub outbitwidth: u64,
    // enumeration
    pub enums: IndexMap<Rc<String>, VelosiAstUnitEnumVariant>,
    // enums defined on the unit
    pub methods: IndexMap<String, Rc<VelosiAstMethod>>,
    /// the location of the enum definition
    pub loc: VelosiTokenStream,
}

impl VelosiAstUnitEnum {
    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeUnitDef,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstUnit, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // create a new context in the symbol table
        st.create_context("unit".to_string());

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

        // TODO: handle the drivation...

        let mut enums: IndexMap<Rc<String>, VelosiAstUnitEnumVariant> = IndexMap::new();
        let mut inbitwidth = 0;
        let outbitwidth = 0;

        for node in pt.nodes.into_iter() {
            match node {
                VelosiParseTreeUnitNode::EnumEntry(e) => {
                    // covert the identifiers..
                    let ident = VelosiAstIdentifier::from(e.ident);

                    if let Some(v) = enums.get(ident.ident()) {
                        let err = VelosiAstErrDoubleDef::new(
                            ident.ident.clone(),
                            v.ident.loc.clone(),
                            ident.loc.clone(),
                        );
                        issues.push(err.into());
                        continue;
                    }

                    let args: Vec<VelosiAstIdentifier> = e
                        .params
                        .into_iter()
                        .map(|p| {
                            let id = VelosiAstIdentifier::from(p);
                            utils::check_param_exists(&mut issues, st, &id);
                            id
                        })
                        .collect();

                    let mut differentiator = Vec::new();

                    let mut has_memory_state = false;
                    if let Some(sym) = st.lookup(ident.ident()) {
                        if let VelosiAstNode::Unit(u) = &sym.ast_node {
                            has_memory_state = u.has_memory_state();
                            if let VelosiAstUnit::Enum(e) = u {
                                let msg = format!(
                                    "unit `{ident}` is an enum. nested enums are not supported"
                                );
                                // let hint = "merge the two enums together";
                                let err = VelosiAstErrBuilder::err(msg)
                                    // .add_hint(hint.to_string())
                                    .add_location(ident.loc.clone())
                                    .add_related_location(
                                        "merge with this enum".to_string(),
                                        e.loc.clone(),
                                    )
                                    .build();
                                issues.push(err);
                            }

                            if inbitwidth == 0 {
                                inbitwidth = u.input_bitwidth();
                            } else if inbitwidth != u.input_bitwidth() {
                                let msg = format!(
                                    "unit `{ident}` has a different inbitwidth to the enum"
                                );
                                let hint = format!(
                                    "expected {} bits but referenced unit has {}",
                                    inbitwidth,
                                    u.input_bitwidth()
                                );
                                let err = VelosiAstErrBuilder::err(msg)
                                    .add_hint(hint)
                                    .add_location(ident.loc.clone())
                                    .build();
                                issues.push(err);
                            }

                            // if outbitwidth == 0 {
                            //     outbitwidth = u.output_bitwidth();
                            // } else if outbitwidth != u.output_bitwidth() {
                            //     let msg = format!("unit `{}` has a different outbitwidth to the enum", ident);
                            //     let hint = format!("expected {} bits but referenced unit has {}", outbitwidth, u.output_bitwidth());
                            //     let err = VelosiAstErrBuilder::err(msg)
                            //     .add_hint(hint)
                            //     .add_location(ident.loc.clone())
                            //     .build();
                            //     issues.push(err);
                            // }

                            // populate the differentiator with the requires of the unit, this may
                            // be reduced later on
                            if let Some(m) = u.get_method("translate") {
                                let pre = m.requires.iter().filter_map(|expr| {
                                    if expr.has_state_references() {
                                        Some(expr.clone())
                                    } else {
                                        None
                                    }
                                });

                                differentiator.extend(pre);
                            }

                            // now we need to match
                            let nparam = u.params_as_slice().len();
                            let nargs = args.len();

                            if nparam != nargs {
                                let msg = format!(
                                    "this unit takes {} argument{} but {} argument{} supplied",
                                    nparam,
                                    if nparam == 1 { "" } else { "s" },
                                    nargs,
                                    if nargs == 1 { "s were" } else { " was" }
                                );

                                let (hint, loc) = if nparam < nargs {
                                    // too many arguments
                                    let hint = format!(
                                        "remove the {} unexpected argument{}",
                                        nargs - nparam,
                                        if nargs - nparam == 1 { "" } else { "s" }
                                    );
                                    let mut loc = args[nparam].loc.clone();
                                    loc.expand_until_end(&args[nargs - 1].loc);
                                    (hint, loc)
                                } else {
                                    // to few arguments
                                    let hint = format!(
                                        "add the {} missing argument{}",
                                        nparam - nargs,
                                        if nparam - nargs == 1 { "" } else { "s" }
                                    );
                                    let loc = if nargs == 0 {
                                        ident.loc.clone()
                                    } else {
                                        args[nargs - 1].loc.clone()
                                    };
                                    (hint, loc)
                                };

                                let err = VelosiAstErrBuilder::err(msg)
                                    .add_hint(hint)
                                    .add_location(loc)
                                    //.add_related_location("parameters defined here".to_string(), m.loc.clone())
                                    .build();
                                issues.push(err);
                            }

                            for (i, arg) in args.iter().enumerate() {
                                if i >= nparam {
                                    let msg = "unexpected argument";
                                    let hint = "remove this argument to the unit instantiation";
                                    let err = VelosiAstErrBuilder::err(msg.to_string())
                                        .add_hint(hint.to_string())
                                        .add_location(arg.loc.clone())
                                        .build();
                                    issues.push(err);
                                    continue;
                                }

                                let param = &u.params_as_slice()[i];

                                // let's force the same same name for now to avoid checking for
                                // renaming, plus the types must match exactly.

                                if param.ident().as_str() != arg.ident().as_str() {
                                    let msg = "inconsistency with unit parameter name";
                                    let hint = format!(
                                        "change this argument to `{}`",
                                        param.ident().as_str()
                                    );

                                    let err = VelosiAstErrBuilder::err(msg.to_string())
                                        .add_hint(hint)
                                        .add_location(arg.loc.clone())
                                        .build();
                                    issues.push(err);
                                }

                                if let Some(s) = st.lookup(arg.ident()) {
                                    if let VelosiAstNode::Param(p) = &s.ast_node {
                                        // there is a unit with that type, so we're good
                                        if !param.ptype.typeinfo.compatible(&p.ptype.typeinfo) {
                                            let msg = "mismatched types";
                                            let hint = format!(
                                                "types not compatible expected {}, found {}",
                                                param.ptype, p.ptype
                                            );
                                            let err = VelosiAstErrBuilder::err(msg.to_string())
                                                .add_hint(hint)
                                                .add_location(arg.loc.clone())
                                                .build();
                                            issues.push(err);
                                        }

                                        if param.ptype.typeinfo != p.ptype.typeinfo {
                                            let msg = "mismatched types";
                                            let hint = format!(
                                                "types must match exactly. expected {}, found {}",
                                                param.ptype, p.ptype
                                            );
                                            let err = VelosiAstErrBuilder::err(msg.to_string())
                                                .add_hint(hint)
                                                .add_location(arg.loc.clone())
                                                .build();
                                            issues.push(err);
                                        }
                                    } else {
                                        unreachable!()
                                    }
                                } else {
                                    let msg = "undefined symbol";
                                    let hint = format!(
                                        "argument `{}` is unknown. Add `{}` to the unit parameters",
                                        arg.ident(),
                                        param.ident()
                                    );

                                    let err = VelosiAstErrBuilder::err(msg.to_string())
                                        .add_hint(hint)
                                        .add_location(arg.loc.clone())
                                        .build();
                                    issues.push(err);
                                }
                            }
                        } else {
                            let err =
                                VelosiAstErrUndef::from_ident_with_other(&ident, sym.loc().clone());
                            issues.push(err.into());
                        }
                    } else {
                        let err = VelosiAstErrUndef::from_ident(&ident);
                        issues.push(err.into());
                    }

                    let val = VelosiAstUnitEnumVariant {
                        ident,
                        args,
                        differentiator,
                        has_memory_state,
                    };

                    enums.insert(val.ident.ident.clone(), val);
                }
                VelosiParseTreeUnitNode::Const(_) => {
                    unit_ignore_node!(VelosiParseTreeUnitNode::Const, node, &mut issues, "Enum")
                }
                VelosiParseTreeUnitNode::InBitWidth(_, _) => todo!(),
                VelosiParseTreeUnitNode::OutBitWidth(_, _) => todo!(),
                VelosiParseTreeUnitNode::Flags(_) => {
                    unit_ignore_node!(VelosiParseTreeUnitNode::Flags, node, &mut issues, "Enum")
                }
                VelosiParseTreeUnitNode::State(_) => {
                    unit_ignore_node!(VelosiParseTreeUnitNode::State, node, &mut issues, "Enum")
                }
                VelosiParseTreeUnitNode::Interface(_) => {
                    unit_ignore_node!(
                        VelosiParseTreeUnitNode::Interface,
                        node,
                        &mut issues,
                        "Enum"
                    )
                }
                VelosiParseTreeUnitNode::Method(_) => {
                    unit_ignore_node!(VelosiParseTreeUnitNode::Method, node, &mut issues, "Enum")
                }
                VelosiParseTreeUnitNode::Map(_) => {
                    unit_ignore_node!(VelosiParseTreeUnitNode::Map, node, &mut issues, "Enum")
                }
                VelosiParseTreeUnitNode::Type(_) => {
                    unit_ignore_node!(VelosiParseTreeUnitNode::Type, node, &mut issues, "Enum")
                }
            }
        }

        for (_, vi) in enums.iter() {
            for (_, vj) in enums.iter() {
                let unit1_sym = st
                    .lookup(vi.ident.ident())
                    .expect("BUG: no unit with that identifier");
                let unit2_sym = st
                    .lookup(vj.ident.ident())
                    .expect("BUG: no unit with that identifier");

                match (&unit1_sym.ast_node, &unit2_sym.ast_node) {
                    (VelosiAstNode::Unit(unit1), VelosiAstNode::Unit(unit2)) => {
                        // TODO: Give more details on what doesn't compare
                        if !unit1.compare_state(unit2) {
                            let msg = "Units in enum have incompatible state";
                            let hint = "This unit has incompatible state with another unit in the same enum";
                            let msg2 = "This is the other unit with incompatible state";
                            let err = VelosiAstErrBuilder::err(msg.to_string())
                                .add_hint(hint.to_string())
                                .add_location(vi.ident.loc.clone())
                                .add_related_location(msg2.to_string(), vj.ident.loc.clone())
                                .build();
                            issues.push(err);
                        }

                        if !unit1.compare_interface(unit2) {
                            let msg = "Units in enum have incompatible interface";
                            let hint = "This unit has incompatible interface with another unit in the same enum";
                            let msg2 = "This is the other unit with incompatible interface";
                            let err = VelosiAstErrBuilder::err(msg.to_string())
                                .add_hint(hint.to_string())
                                .add_location(vi.ident.loc.clone())
                                .add_related_location(msg2.to_string(), vj.ident.loc.clone())
                                .build();
                            issues.push(err);
                        }
                    }
                    _ => unreachable!(),
                }
            }
        }

        let mut methods = IndexMap::new();
        methods.insert("map".to_string(), Rc::new(VelosiAstMethod::default_map()));
        methods.insert(
            "unmap".to_string(),
            Rc::new(VelosiAstMethod::default_unmap()),
        );
        methods.insert(
            "protect".to_string(),
            Rc::new(VelosiAstMethod::default_protect()),
        );

        let ident = VelosiAstIdentifier::from(pt.name);
        utils::check_camel_case(&mut issues, &ident);

        let res = Self {
            ident,
            params,
            inbitwidth,
            outbitwidth,
            enums,
            methods,
            loc: pt.loc,
        };

        // and restore the context again.
        st.drop_context();

        ast_result_return!(VelosiAstUnit::Enum(Rc::new(res)), issues)
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

    pub fn params_as_slice(&self) -> &[Rc<VelosiAstParam>] {
        self.params.as_slice()
    }

    pub fn vaddr_max(&self) -> u64 {
        if self.inbitwidth < 64 {
            (1u64 << self.inbitwidth) - 1
        } else {
            u64::MAX
        }
    }

    pub fn paddr_max(&self) -> u64 {
        if self.outbitwidth < 64 {
            (1u64 << self.outbitwidth) - 1
        } else {
            u64::MAX
        }
    }

    pub fn get_next_unit_idents(&self) -> Vec<&Rc<String>> {
        self.enums.keys().collect()
    }

    /// obtains the (unit, differentiators) for all units of the enum
    ///
    /// The differentiator expressions are returned as a slice of boolean expressions forming
    /// a conjunctive normal form
    pub fn get_unit_differentiators(&self) -> HashMap<Rc<String>, &[Rc<VelosiAstExpr>]> {
        self.enums
            .iter()
            .map(|(k, v)| (k.clone(), v.differentiator.as_slice()))
            .collect()
    }

    /// obtains the differentiator expression over the state for the supplied unit identifier
    ///
    /// The differentiator expressions are returned as a slice of boolean expressions forming
    /// a conjunctive normal form
    pub fn get_unit_differentiator(&self, unit: &Rc<String>) -> &[Rc<VelosiAstExpr>] {
        if let Some(variant) = self.enums.get(unit) {
            variant.differentiator.as_slice()
        } else {
            &[]
        }
    }

    /// sets the differentiator expression over the state for the supplied unit identifier
    pub fn set_unit_differentiator(
        &mut self,
        unit: &Rc<String>,
        differentiator: Vec<Rc<VelosiAstExpr>>,
    ) {
        self.enums
            .get_mut(unit)
            .expect("unit to be found")
            .differentiator = differentiator;
    }

    pub fn has_memory_state(&self) -> bool {
        self.enums.values().any(|v| v.has_memory_state)
    }

    pub fn in_memory_state_size(&self, units: &HashMap<Rc<String>, VelosiAstUnit>) -> u64 {
        if let Some(unit) = self.enums.first() {
            // XXX: assuming all units have the same state here
            let dst = units.get(unit.0).unwrap();
            dst.in_memory_state_size(units)
        } else {
            0
        }
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
}

/// Implementation of [Display] for [VelosiAstUnitEnum]
impl Display for VelosiAstUnitEnum {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "enum {} (", self.ident)?;
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            Display::fmt(p, f)?;
        }
        write!(f, ")")?;
        writeln!(f, " {{")?;

        writeln!(f)?;
        writeln!(f, "  inbitwidth = {};", self.inbitwidth)?;
        writeln!(f, "  outbitwidth = {};\n", self.outbitwidth)?;

        if !self.enums.is_empty() {
            writeln!(f)?;
            for (e, p) in &self.enums {
                write!(f, "  {e}(")?;
                for (i, p) in p.args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{p}")?;
                }
                writeln!(f, "  ),")?;
            }
        }

        write!(f, "\n}}")
    }
}

/// Implementation of [Debug] for [VelosiAstUnitEnum]
impl Debug for VelosiAstUnitEnum {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
