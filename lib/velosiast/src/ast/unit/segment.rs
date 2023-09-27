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
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used third-party crates
use indexmap::{
    map::{Values, ValuesMut},
    IndexMap,
};

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
    method::{
        FN_SIG_MAP, FN_SIG_MATCHFLAGS, FN_SIG_PROTECT, FN_SIG_TRANSLATE, FN_SIG_UNMAP, FN_SIG_VALID,
    },
    VelosiAstConst, VelosiAstExpr, VelosiAstFlags, VelosiAstIdentifier, VelosiAstInterface,
    VelosiAstMethod, VelosiAstNode, VelosiAstParam, VelosiAstState, VelosiAstStateField,
    VelosiAstUnit, VelosiOperation,
};

#[derive(PartialEq, Eq, Clone)]
pub struct VelosiAstUnitSegment {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// whether the unit is abstract
    pub is_abstract: bool,

    /// the parameters of the unit
    pub params: Vec<Rc<VelosiAstParam>>,
    /// the base class
    pub derived: Option<Rc<VelosiAstIdentifier>>,

    pub inbitwidth: u64,
    pub outbitwidth: u64,

    /// the state of the unit
    pub state: Rc<VelosiAstState>,
    /// the interface of the unit
    pub interface: Rc<VelosiAstInterface>,
    ///
    pub consts: IndexMap<String, Rc<VelosiAstConst>>,

    pub flags: Option<Rc<VelosiAstFlags>>,

    pub methods: IndexMap<String, Rc<VelosiAstMethod>>,

    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstUnitSegment {
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

        let mut methods = IndexMap::new();
        let mut consts = IndexMap::new();

        let mut inbitwidth = None;
        let mut derived_inbitwidth = None;
        let mut outbitwidth = None;
        let mut derived_outbitwidth = None;

        let mut flags: Option<Rc<VelosiAstFlags>>;
        let mut derived_flags: Option<Rc<VelosiAstFlags>> = None;

        let mut interface: Option<Rc<VelosiAstInterface>> = None;
        let mut derived_interface: Option<Rc<VelosiAstInterface>> = None;

        let mut state: Option<Rc<VelosiAstState>> = None;
        let mut derived_state: Option<Rc<VelosiAstState>> = None;

        let derived = if let Some(d) = pt.derived {
            let d = VelosiAstIdentifier::from(d);
            utils::check_type_exists(&mut issues, st, &d);
            Some(Rc::new(d))
        } else {
            None
        };

        if let Some(d) = &derived {
            let sym = st.lookup(d.path()).unwrap();
            let unit = if let VelosiAstNode::Unit(u) = &sym.ast_node {
                u
            } else {
                unreachable!();
            };

            // only do derives for segments
            if !unit.is_segment() {
                let msg = "Derived unit is not a `segment` type.";
                let hint = "Change this to a `staticmap`, or add a state definition.";
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(pt.loc.from_self_with_subrange(0..1))
                    .build();
                issues.push(err);
            }

            // merge all the constants
            for c in unit.consts() {
                consts.insert(c.ident_to_string(), c.clone());
            }

            // merge all the methods, we'll deal with overwriting abstract ones later
            for m in unit.methods() {
                methods.insert(m.ident_to_string(), m.clone());
            }

            derived_inbitwidth = Some(unit.input_bitwidth());
            inbitwidth = Some((unit.input_bitwidth(), unit.loc().clone()));

            derived_outbitwidth = Some(unit.output_bitwidth());
            outbitwidth = Some((unit.output_bitwidth(), unit.loc().clone()));

            derived_interface = unit.interface();
            interface = unit.interface();

            derived_state = unit.state();
            state = unit.state();

            derived_flags = unit.flags();
        }

        // add the elements to the symbol table
        let sym = st.lookup("flags").unwrap();
        if let VelosiAstNode::Flags(u) = &sym.ast_node {
            flags = Some(u.clone());
        } else {
            unreachable!();
        };

        consts.values().for_each(|c| {
            st.insert(c.clone().into())
                .expect("could not insert into symbol table")
        });

        methods.values().for_each(|c| {
            st.insert(c.clone().into())
                .expect("could not insert into symbol table")
        });

        if let Some(f) = &flags {
            st.insert(f.clone().into()).ok();
        }

        if let Some(i) = &interface {
            i.update_symbol_table(st);
            st.insert(i.clone().into())
                .expect("could not insert into symbol table")
        }

        if let Some(s) = &state {
            s.update_symbol_table(st);
            st.insert(s.clone().into())
                .expect("could not insert into symbol table")
        }

        // now process the new nodes defined in this unit

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
                VelosiParseTreeUnitNode::InBitWidth(e, loc) => {
                    let e = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(e, st), issues);

                    let w = if let Some(w) = e.const_expr_result_num() {
                        w
                    } else {
                        let msg = "Input bitwidth must be a constant expression.";
                        let hint = "Change `{}` to a constant expression (e.g, 64).";
                        let err = VelosiAstErrBuilder::err(msg.to_string())
                            .add_hint(hint.to_string())
                            .add_location(loc.clone())
                            .build();
                        issues.push(err);
                        // just assigning 64 for now...
                        64
                    };

                    utils::check_addressing_width(&mut issues, w, loc.clone());
                    if inbitwidth.is_some() && derived_inbitwidth.is_none() {
                        let err = VelosiAstErrDoubleDef::new(
                            Rc::new(String::from("inbitwidth")),
                            inbitwidth.as_ref().unwrap().1.clone(),
                            loc.clone(),
                        );
                        issues.push(err.into());
                    } else {
                        inbitwidth = Some((w, loc));
                    }
                }
                VelosiParseTreeUnitNode::OutBitWidth(e, loc) => {
                    let e = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(e, st), issues);

                    let w = if let Some(w) = e.const_expr_result_num() {
                        w
                    } else {
                        let msg = "Output bitwidth must be a constant expression.";
                        let hint = "Change `{}` to a constant expression (e.g, 64).";
                        let err = VelosiAstErrBuilder::err(msg.to_string())
                            .add_hint(hint.to_string())
                            .add_location(loc.clone())
                            .build();
                        issues.push(err);
                        // just assigning 64 for now...
                        64
                    };

                    utils::check_addressing_width(&mut issues, w, loc.clone());
                    if outbitwidth.is_some() && derived_outbitwidth.is_none() {
                        let err = VelosiAstErrDoubleDef::new(
                            Rc::new(String::from("outbitwidth")),
                            outbitwidth.as_ref().unwrap().1.clone(),
                            loc.clone(),
                        );
                        issues.push(err.into());
                    } else {
                        outbitwidth = Some((w, loc));
                    }
                }
                VelosiParseTreeUnitNode::Flags(f) => {
                    let mut flgs = ast_result_unwrap!(VelosiAstFlags::from_parse_tree(f), issues);

                    // add a deprecation warning
                    let msg = "defining flags in unit context is deprecated.";
                    let err = VelosiAstErrBuilder::warn(msg.to_string())
                        .add_hint("define flags globally instead.".to_string())
                        .add_location(flgs.loc.clone())
                        .build();
                    issues.push(err);

                    // check for double definition
                    if flags.is_some() && derived_flags.is_none() {
                        let f = flags.as_ref().unwrap();
                        let err = VelosiAstErrDoubleDef::new(
                            Rc::new(String::from("flags")),
                            f.loc.clone(),
                            flgs.loc.clone(),
                        );
                        issues.push(err.into());
                    } else {
                        if let Some(d) = derived_flags.take() {
                            flgs.derive_from(&d);
                        }
                        let flgs = Rc::new(flgs);
                        flags = Some(flgs);
                    }

                    match (&flags, st.lookup("flags")) {
                        (Some(flgs), Some(sym)) => {
                            if let VelosiAstNode::Flags(f) = &sym.ast_node {
                                // we have some flags that are defined
                                if f.as_ref() != flgs.as_ref() {
                                    // they are not the same, this is an error!
                                    let msg = "Flags definition mismatch";
                                    let err = VelosiAstErrBuilder::err(msg.to_string())
                                        .add_hint(
                                            "ensure flags definitions are identical".to_string(),
                                        )
                                        .add_location(flgs.loc.clone())
                                        .add_related_location(
                                            "this is the previous definition".to_string(),
                                            f.loc.clone(),
                                        )
                                        .build();
                                    issues.push(err);
                                } else {
                                    // they are the same, so leave let's just take the globally defined
                                    flags = Some(f.clone());
                                }
                            }
                        }
                        (Some(flgs), _) => {
                            let msg = "using unit flags as the new global flags!";
                            let err = VelosiAstErrBuilder::warn(msg.to_string())
                                .add_location(flgs.loc.clone())
                                .build();
                            issues.push(err);

                            st.insert_root(flgs.clone().into())
                                .expect("could not insert flags into symbol table");
                        }
                        _ => {}
                    }
                }
                VelosiParseTreeUnitNode::State(pst) => {
                    let mut state_def =
                        ast_result_unwrap!(VelosiAstState::from_parse_tree(pst, st), issues);
                    if state.is_some() && derived_state.is_none() {
                        let st = state.as_ref().unwrap();
                        let err = VelosiAstErrDoubleDef::new(
                            Rc::new(String::from("state")),
                            st.loc().clone(),
                            state_def.loc().clone(),
                        );
                        issues.push(err.into());
                    } else {
                        if let Some(d) = derived_state.take() {
                            state_def.derive_from(&d);
                            state_def.update_symbol_table(st);
                        }

                        let s = Rc::new(state_def);
                        st.update(s.clone().into())
                            .expect("state already exists in symbolt able?");
                        state = Some(s);
                    }
                }
                VelosiParseTreeUnitNode::Interface(pst) => {
                    let mut iface_def =
                        ast_result_unwrap!(VelosiAstInterface::from_parse_tree(pst, st), issues);

                    if interface.is_some() && derived_interface.is_none() {
                        let st = interface.as_ref().unwrap();
                        let err = VelosiAstErrDoubleDef::new(
                            Rc::new(String::from("interface")),
                            st.loc().clone(),
                            iface_def.loc().clone(),
                        );
                        issues.push(err.into());
                    } else {
                        if let Some(d) = derived_interface.take() {
                            iface_def.derive_from(&d);
                            iface_def.update_symbol_table(st);
                        }
                        let s = Rc::new(iface_def);
                        st.update(s.clone().into())
                            .expect("interface already exists in symbolt able?");
                        interface = Some(s);
                    }
                }
                VelosiParseTreeUnitNode::Method(method) => {
                    let m = Rc::new(ast_result_unwrap!(
                        VelosiAstMethod::from_parse_tree(method, st),
                        issues
                    ));

                    if m.is_extern {
                        let msg = "segment specifications do not allow extern functions";
                        let hint = "remove this method or make it non-extern";
                        let err = VelosiAstErrBuilder::err(msg.to_string())
                            .add_hint(hint.to_string())
                            .add_location(m.loc.from_self_with_subrange(0..1))
                            .build();
                        issues.push(err);
                    }

                    if let Some(mderiv) = st.lookup(m.ident().as_str()) {
                        // exists already,
                        if let VelosiAstNode::Method(md) = &mderiv.ast_node {
                            if md.is_abstract {
                                methods.insert(m.ident_to_string(), m);
                            } else {
                                // double defined!
                                let err = VelosiAstErrDoubleDef::new(
                                    m.ident().clone(),
                                    md.loc.clone(),
                                    m.loc.clone(),
                                );
                                issues.push(err.into());
                            }
                        } else {
                            // differnet kind of symbol....
                            let err = VelosiAstErrUndef::with_other(
                                m.ident().clone(),
                                m.loc.clone(),
                                mderiv.loc().clone(),
                            );
                            issues.push(err.into());
                        }
                    } else {
                        st.insert(m.clone().into())
                            .expect("method already exists in symbol table?");
                        methods.insert(m.ident_to_string(), m);
                    }
                }
                VelosiParseTreeUnitNode::EnumEntry(_) => unit_ignore_node!(
                    VelosiParseTreeUnitNode::EnumEntry,
                    node,
                    &mut issues,
                    "Segments"
                ),
                VelosiParseTreeUnitNode::Type(_) => {
                    todo!("handle me")
                }
                VelosiParseTreeUnitNode::Map(_) => {
                    unit_ignore_node!(VelosiParseTreeUnitNode::Map, node, &mut issues, "Segments")
                }
            }
        }

        let state = if let Some(st) = state {
            st
        } else {
            if !pt.is_abstract {
                let msg = "Segment unit has no state definition";
                let hint = "Change this to a `staticmap`, or add a state definition.";
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(pt.loc.from_self_with_subrange(0..1))
                    .build();
                issues.push(err);
            }

            Rc::new(VelosiAstState::default())
        };

        let interface = if let Some(i) = interface {
            i
        } else {
            if !pt.is_abstract {
                let msg = "Segment unit has no interface definition";
                let hint = "Change this to a `staticmap`, or add an interface definition.";
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(pt.loc.from_self_with_subrange(0..1))
                    .build();
                issues.push(err);
            }

            Rc::new(VelosiAstInterface::default())
        };

        if !methods.contains_key("map") && !pt.is_abstract {
            let msg = "Segment unit has no `map` method defined. Using default implementation";
            let hint = format!("add method with signature `{FN_SIG_MAP}` to unit");
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_map());
            methods.insert(m.ident_to_string(), m);
        }

        if !methods.contains_key("unmap") && !pt.is_abstract {
            let msg = "Segment unit has no `unmap` method defined. Using default implementation";
            let hint = format!("add method with signature `{FN_SIG_UNMAP}` to unit");
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_unmap());
            methods.insert(m.ident_to_string(), m);
        }

        if !methods.contains_key("protect") && !pt.is_abstract {
            let msg = "Segment unit has no `protect` method defined. Using default implementation";
            let hint = format!("add method with signature `{FN_SIG_PROTECT}` to unit");
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_protect());
            methods.insert(m.ident_to_string(), m);
        }

        if !methods.contains_key("valid") && !pt.is_abstract {
            let msg = "Segment unit has no `valid` method defined. Using default implementation";
            let hint = format!("add method with signature `{FN_SIG_VALID}` to unit");
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_valid());
            methods.insert(m.ident_to_string(), m);
        }

        if !methods.contains_key("translate") && !pt.is_abstract {
            let msg = "Segment unit has no `protect` method defined. Using default implementation";
            let hint = format!("add method with signature `{FN_SIG_TRANSLATE}` to unit");
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_translate());
            methods.insert(m.ident_to_string(), m);
        }

        if !methods.contains_key("matchflags") && !pt.is_abstract {
            let msg = "Segment unit has no `protect` method defined. Using default implementation";
            let hint = format!("add method with signature `{FN_SIG_MATCHFLAGS}` to unit");
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_matchflags());
            methods.insert(m.ident_to_string(), m);
        }

        // check the methods whether they are still abstract
        if !pt.is_abstract {
            for m in methods.values() {
                if m.is_abstract {
                    let msg = format!(
                        "Method `{}::{}` is declared abstract, but enclosing unit is not.",
                        pt.name,
                        m.ident(),
                    );
                    let hint = "Remove the abstract modifier or make the unit abstract.";
                    let err = VelosiAstErrBuilder::err(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(m.loc.from_self_with_subrange(0..1))
                        .build();
                    issues.push(err);
                }
            }
        }

        let inbitwidth = if let Some((ibw, _)) = inbitwidth {
            ibw
        } else {
            if !pt.is_abstract {
                let msg = "Unit has no input bitwidth definition. Assuming 64 bits.";
                let err = VelosiAstErrBuilder::warn(msg.to_string())
                    .add_location(pt.loc.from_self_with_subrange(0..1))
                    .build();
                issues.push(err);
            }

            64
        };

        let outbitwidth = if let Some((obw, _)) = outbitwidth {
            obw
        } else {
            if !pt.is_abstract {
                let msg = "Unit has no output bitwidth definition. Assuming 64 bits.";
                let err = VelosiAstErrBuilder::warn(msg.to_string())
                    .add_location(pt.loc.from_self_with_subrange(0..1))
                    .build();
                issues.push(err);
            }

            64
        };

        let ident = VelosiAstIdentifier::from(pt.name);
        utils::check_camel_case(&mut issues, &ident);

        let res = Self {
            ident,
            is_abstract: pt.is_abstract,
            params,
            derived,
            inbitwidth,
            outbitwidth,
            state,
            interface,
            consts,
            flags,
            methods,
            loc: pt.loc,
        };

        // and restore the context again.
        st.drop_context();

        ast_result_return!(VelosiAstUnit::Segment(Rc::new(res)), issues)
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

    pub fn get_method(&self, name: &str) -> Option<&Rc<VelosiAstMethod>> {
        self.methods.get(name)
    }

    pub fn methods(&self) -> Values<String, Rc<VelosiAstMethod>> {
        self.methods.values()
    }

    pub fn methods_mut(&mut self) -> ValuesMut<String, Rc<VelosiAstMethod>> {
        self.methods.values_mut()
    }

    pub fn consts(&self) -> Values<String, Rc<VelosiAstConst>> {
        self.consts.values()
    }

    pub fn consts_mut(&mut self) -> ValuesMut<String, Rc<VelosiAstConst>> {
        self.consts.values_mut()
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

    pub fn set_method_ops(&mut self, method: &str, ops: Vec<VelosiOperation>) {
        if let Some(m) = self.methods.get_mut(method) {
            if let Some(m) = Rc::get_mut(m) {
                m.ops = ops;
            } else {
                panic!(
                    "Failed to obtain mut reference to method `{}` (refs: {}/{})",
                    method,
                    Rc::strong_count(m),
                    Rc::weak_count(m)
                );
            }
        } else {
            unreachable!("method {} not found", method);
        }
    }

    pub fn get_state_registers(&self) -> Vec<Rc<VelosiAstStateField>> {
        self.state.get_registers()
    }

    pub fn get_next_unit_idents(&self) -> Vec<&Rc<String>> {
        self.methods
            .get("map")
            .and_then(|m| m.get_param("pa"))
            .and_then(|p| p.ptype.typeref())
            .map(|t| vec![t])
            .unwrap_or_default()
    }
}

/// Implementation of [Display] for [VelosiAstUnitSegment]
impl Display for VelosiAstUnitSegment {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if self.is_abstract {
            write!(f, "abstract ")?;
        }
        write!(f, "segment {} (", self.ident)?;
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            Display::fmt(p, f)?;
        }
        write!(f, ")")?;
        if let Some(d) = &self.derived {
            write!(f, " : {d}")?;
        }
        writeln!(f, " {{")?;

        if !self.consts.is_empty() {
            writeln!(f)?;
            for c in self.consts.values() {
                let formatted = format!("{c}");
                for line in formatted.lines() {
                    writeln!(f, "  {line}")?;
                }
            }
        }

        writeln!(f)?;
        writeln!(f, "  inbitwidth = {};", self.inbitwidth)?;
        writeln!(f, "  outbitwidth = {};", self.outbitwidth)?;

        if let Some(flags) = &self.flags {
            writeln!(f)?;
            write!(f, "  flags = ")?;
            Display::fmt(flags, f)?;
            writeln!(f, ";")?;
        }

        writeln!(f)?;
        let formatted = format!("{}", self.state);
        for line in formatted.lines() {
            writeln!(f, "  {line}")?;
        }

        writeln!(f)?;
        let formatted = format!("{}", self.interface);
        for line in formatted.lines() {
            writeln!(f, "  {line}")?;
        }

        if !self.methods.is_empty() {
            for method in self.methods.values() {
                let formatted = format!("{method}");
                writeln!(f)?;
                for line in formatted.lines() {
                    writeln!(f, "  {line}")?;
                }
            }
        }

        write!(f, "\n}}")
    }
}

/// Implementation of [Debug] for [VelosiAstUnitSegment]
impl Debug for VelosiAstUnitSegment {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
