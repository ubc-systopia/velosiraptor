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
    VelosiParseTreeUnit, VelosiParseTreeUnitDef, VelosiParseTreeUnitNode, VelosiTokenStream,
};

use crate::ast::{
    method::{FN_SIG_MAP, FN_SIG_MATCHFLAGS, FN_SIG_PROTECT, FN_SIG_TRANSLATE, FN_SIG_UNMAP},
    types::{VelosiAstType, VelosiAstTypeInfo},
    VelosiAstConst, VelosiAstInterface, VelosiAstMethod, VelosiAstNode, VelosiAstParam,
    VelosiAstStaticMap,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstErrDoubleDef, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

use super::flags::VelosiAstFlags;
use super::{VelosiAstIdentifier, VelosiAstState};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstUnitSegment {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
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
    pub consts: Vec<Rc<VelosiAstConst>>,
    pub consts_map: HashMap<String, Rc<VelosiAstConst>>,

    pub flags: Option<Rc<VelosiAstFlags>>,

    pub methods: Vec<Rc<VelosiAstMethod>>,
    pub methods_map: HashMap<String, Rc<VelosiAstMethod>>,

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
        for p in pt.params.into_iter() {
            let param = Rc::new(ast_result_unwrap!(
                VelosiAstParam::from_parse_tree(p, false, st),
                issues
            ));

            // add the param to the symbol table, if it doesn't exist already
            if let Err(e) = st.insert(param.clone().into()) {
                issues.push(e);
            } else {
                params.push(param);
            }
        }

        let derived = if let Some(d) = pt.derived {
            let d = VelosiAstIdentifier::from(d);
            utils::check_type_exists(&mut issues, st, &d);
            Some(Rc::new(d))
        } else {
            None
        };

        // TODO: handle the drivation...

        let mut methods_map = HashMap::new();
        let mut methods = Vec::new();
        let mut consts_map = HashMap::new();
        let mut consts = Vec::new();
        let mut inbitwidth = None;
        let mut outbitwidth = None;
        let mut flags: Option<Rc<VelosiAstFlags>> = None;
        let mut interface: Option<Rc<VelosiAstInterface>> = None;
        let mut state: Option<Rc<VelosiAstState>> = None;
        for node in pt.nodes.into_iter() {
            match node {
                VelosiParseTreeUnitNode::Const(c) => {
                    let c = Rc::new(ast_result_unwrap!(
                        VelosiAstConst::from_parse_tree(c, st),
                        issues
                    ));
                    if let Err(e) = st.insert(c.clone().into()) {
                        issues.push(e);
                    } else {
                        consts.push(c.clone());
                        consts_map.insert(c.ident_to_string(), c);
                    }
                }
                VelosiParseTreeUnitNode::InBitWidth(w, loc) => {
                    utils::check_addressing_width(&mut issues, w, loc);
                    inbitwidth = Some(w);
                }
                VelosiParseTreeUnitNode::OutBitWidth(w, loc) => {
                    utils::check_addressing_width(&mut issues, w, loc);
                    outbitwidth = Some(w);
                }
                VelosiParseTreeUnitNode::Flags(f) => {
                    let flgs = Rc::new(ast_result_unwrap!(
                        VelosiAstFlags::from_parse_tree(f),
                        issues
                    ));
                    if let Some(f) = &flags {
                        let err = VelosiAstErrDoubleDef::new(
                            Rc::new(String::from("flags")),
                            f.loc.clone(),
                            flgs.loc.clone(),
                        );
                        issues.push(err.into());
                    } else {
                        st.insert(flgs.clone().into())
                            .expect("flags already exist n symbol table?");
                        flags = Some(flgs);
                    }
                }
                VelosiParseTreeUnitNode::State(pst) => {
                    let s = Rc::new(ast_result_unwrap!(
                        VelosiAstState::from_parse_tree(pst, st),
                        issues
                    ));
                    if let Some(st) = &state {
                        let err = VelosiAstErrDoubleDef::new(
                            Rc::new(String::from("state")),
                            st.loc().clone(),
                            s.loc().clone(),
                        );
                        issues.push(err.into());
                    } else {
                        st.insert(s.clone().into())
                            .expect("state already exists in symbolt able?");
                        state = Some(s);
                    }
                }
                VelosiParseTreeUnitNode::Interface(pst) => {
                    let s = Rc::new(ast_result_unwrap!(
                        VelosiAstInterface::from_parse_tree(pst, st),
                        issues
                    ));
                    if let Some(st) = &interface {
                        let err = VelosiAstErrDoubleDef::new(
                            Rc::new(String::from("interface")),
                            st.loc().clone(),
                            s.loc().clone(),
                        );
                        issues.push(err.into());
                    } else {
                        st.insert(s.clone().into())
                            .expect("interface already exists in symbolt able?");
                        interface = Some(s);
                    }
                }
                VelosiParseTreeUnitNode::Method(method) => {
                    let m = Rc::new(ast_result_unwrap!(
                        VelosiAstMethod::from_parse_tree(method, st),
                        issues
                    ));
                    if let Err(e) = st.insert(m.clone().into()) {
                        issues.push(e);
                    } else {
                        methods.push(m.clone());
                        methods_map.insert(m.ident_to_string(), m);
                    }
                }
                VelosiParseTreeUnitNode::Map(map) => {
                    let msg = "Ignored unit node: Map definitions are not supported in Segments.";
                    let hint = "Remove the map definition.";
                    let err = VelosiAstErrBuilder::warn(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(map.loc().clone())
                        .build();
                    issues.push(err);
                }
            }
        }

        let state = if let Some(st) = state {
            st
        } else {
            let msg = "Segment unit has no state definition";
            let hint = "Change this to a `staticmap`, or add a state definition.";
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            Rc::new(VelosiAstState::NoneState(pt.loc.clone()))
        };

        if !methods_map.contains_key("map") {
            let msg = "Segment unit has no `map` method defined. Using default implementation";
            let hint = format!("add method with signature `{}` to unit", FN_SIG_MAP);
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_map());
            methods.push(m.clone());
            methods_map.insert(m.ident_to_string(), m);
        }

        if !methods_map.contains_key("unmap") {
            let msg = "Segment unit has no `unmap` method defined. Using default implementation";
            let hint = format!("add method with signature `{}` to unit", FN_SIG_UNMAP);
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_unmap());
            methods.push(m.clone());
            methods_map.insert(m.ident_to_string(), m);
        }

        if !methods_map.contains_key("protect") {
            let msg = "Segment unit has no `protect` method defined. Using default implementation";
            let hint = format!("add method with signature `{}` to unit", FN_SIG_PROTECT);
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_protect());
            methods.push(m.clone());
            methods_map.insert(m.ident_to_string(), m);
        }

        if !methods_map.contains_key("translate") {
            let msg = "Segment unit has no `protect` method defined. Using default implementation";
            let hint = format!("add method with signature `{}` to unit", FN_SIG_TRANSLATE);
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_translate());
            methods.push(m.clone());
            methods_map.insert(m.ident_to_string(), m);
        }

        if !methods_map.contains_key("matchflags") {
            let msg = "Segment unit has no `protect` method defined. Using default implementation";
            let hint = format!("add method with signature `{}` to unit", FN_SIG_MATCHFLAGS);
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_matchflags());
            methods.push(m.clone());
            methods_map.insert(m.ident_to_string(), m);
        }

        let interface = if let Some(i) = interface {
            i
        } else {
            let msg = "Segment unit has no interface definition";
            let hint = "Change this to a `staticmap`, or add an interface definition.";
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            Rc::new(VelosiAstInterface::NoneInterface(pt.loc.clone()))
        };

        let inbitwidth = if let Some(ibw) = inbitwidth {
            ibw
        } else {
            let msg = "Unit has no input bitwidth definition. Assuming 64 bits.";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            64
        };

        let outbitwidth = if let Some(obw) = outbitwidth {
            obw
        } else {
            let msg = "Unit has no output bitwidth definition. Assuming 64 bits.";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            64
        };

        let res = Self {
            ident: VelosiAstIdentifier::from(pt.name),
            params,
            derived,
            inbitwidth,
            outbitwidth,
            state,
            interface,
            consts,
            consts_map,
            flags,
            methods,
            methods_map,
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
        self.methods_map.get(name)
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
}

/// Implementation of [Display] for [VelosiAstUnitSegment]
impl Display for VelosiAstUnitSegment {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "segment {} (", self.ident)?;
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            Display::fmt(p, f)?;
        }
        write!(f, ")")?;
        if let Some(d) = &self.derived {
            write!(f, " : {}", d)?;
        }
        writeln!(f, " {{")?;

        for c in &self.consts {
            write!(f, "  ")?;
            Display::fmt(c, f)?;
            writeln!(f)?;
        }

        if self.consts.is_empty() {
            writeln!(f, "  // no constants")?;
        }
        writeln!(f)?;

        writeln!(f, "  inbitwidth = {};", self.inbitwidth)?;
        writeln!(f, "  outbitwidth = {};\n", self.outbitwidth)?;

        if let Some(flags) = &self.flags {
            write!(f, "  flags = ")?;
            Display::fmt(flags, f)?;
            writeln!(f, ";\n")?;
        } else {
            writeln!(f, "  // no flags\n")?;
        }

        write!(f, "  state = ")?;
        Display::fmt(&self.state, f)?;
        writeln!(f, ";\n")?;

        write!(f, "  interface = ")?;
        Display::fmt(&self.interface, f)?;
        writeln!(f, ";\n")?;

        for (i, m) in self.methods.iter().enumerate() {
            if i > 0 {
                writeln!(f, "\n")?;
            }
            Display::fmt(m, f)?;
        }

        if self.methods.is_empty() {
            write!(f, "  // no methods")?;
        }

        write!(f, "\n}}")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstUnitStaticMap {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the parameters of the unit
    pub params: Vec<Rc<VelosiAstParam>>,
    /// the base class
    pub derived: Option<Rc<VelosiAstIdentifier>>,

    pub inbitwidth: u64,
    pub outbitwidth: u64,

    ///
    pub consts: Vec<Rc<VelosiAstConst>>,
    pub consts_map: HashMap<String, Rc<VelosiAstConst>>,

    pub methods: Vec<Rc<VelosiAstMethod>>,
    pub methods_map: HashMap<String, Rc<VelosiAstMethod>>,

    pub map: VelosiAstStaticMap,

    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstUnitStaticMap {
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
        for p in pt.params.into_iter() {
            let param = Rc::new(ast_result_unwrap!(
                VelosiAstParam::from_parse_tree(p, false, st),
                issues
            ));

            // add the param to the symbol table, if it doesn't exist already
            if let Err(e) = st.insert(param.clone().into()) {
                issues.push(e);
            } else {
                params.push(param);
            }
        }

        let derived = if let Some(d) = pt.derived {
            let d = VelosiAstIdentifier::from(d);
            utils::check_type_exists(&mut issues, st, &d);
            Some(Rc::new(d))
        } else {
            None
        };

        // TODO: handle the drivation...

        let mut methods_map = HashMap::new();
        let mut methods = Vec::new();
        let mut consts_map = HashMap::new();
        let mut consts = Vec::new();
        let mut inbitwidth = None;
        let mut outbitwidth = None;
        let mut map: Option<VelosiAstStaticMap> = None;
        for node in pt.nodes.into_iter() {
            match node {
                VelosiParseTreeUnitNode::Const(c) => {
                    let c = Rc::new(ast_result_unwrap!(
                        VelosiAstConst::from_parse_tree(c, st),
                        issues
                    ));
                    if let Err(e) = st.insert(c.clone().into()) {
                        issues.push(e);
                    } else {
                        consts.push(c.clone());
                        consts_map.insert(c.ident_to_string(), c);
                    }
                }
                VelosiParseTreeUnitNode::InBitWidth(w, loc) => {
                    utils::check_addressing_width(&mut issues, w, loc.clone());
                    inbitwidth = Some((w, loc));
                }
                VelosiParseTreeUnitNode::OutBitWidth(w, loc) => {
                    utils::check_addressing_width(&mut issues, w, loc.clone());
                    outbitwidth = Some((w, loc));
                }
                VelosiParseTreeUnitNode::Flags(f) => {
                    let msg =
                        "Ignored unit node: Flags definitions are not supported in StaticMaps.";
                    let hint = "Remove the flags definition.";
                    let err = VelosiAstErrBuilder::warn(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(f.pos.clone())
                        .build();
                    issues.push(err);
                }
                VelosiParseTreeUnitNode::State(pst) => {
                    let msg =
                        "Ignored unit node: State definitions are not supported in StaticMaps.";
                    let hint = "Remove the state definition.";
                    let err = VelosiAstErrBuilder::warn(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(pst.loc().clone())
                        .build();
                    issues.push(err);
                }
                VelosiParseTreeUnitNode::Interface(pst) => {
                    let msg =
                        "Ignored unit node: Interface definitions are not supported in StaticMaps.";
                    let hint = "Remove the interface definition.";
                    let err = VelosiAstErrBuilder::warn(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(pst.loc().clone())
                        .build();
                    issues.push(err);
                }
                VelosiParseTreeUnitNode::Method(method) => {
                    let m = Rc::new(ast_result_unwrap!(
                        VelosiAstMethod::from_parse_tree(method, st),
                        issues
                    ));
                    if let Err(e) = st.insert(m.clone().into()) {
                        issues.push(e);
                    } else {
                        methods.push(m.clone());
                        methods_map.insert(m.ident_to_string(), m);
                    }
                }
                VelosiParseTreeUnitNode::Map(m) => {
                    let s = ast_result_unwrap!(VelosiAstStaticMap::from_parse_tree(m, st), issues);
                    if let Some(st) = &map {
                        let err = VelosiAstErrDoubleDef::new(
                            Rc::new(String::from("staticmap")),
                            st.loc().clone(),
                            s.loc().clone(),
                        );
                        issues.push(err.into());
                    } else {
                        // st.insert(s.clone().into())
                        //     .expect("interface already exists in symbolt able?");
                        map = Some(s);
                    }
                }
            }
        }

        let loc = pt.loc.from_self_with_subrange(0..2);
        let map = map.unwrap_or_else(|| {
            let msg = "Map definition missing.";
            let hint = "Add a `mapdef = ...` definition to the unit";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_location(loc)
                .add_hint(hint.to_string())
                .build();
            issues.push(err);
            VelosiAstStaticMap::default()
        });

        let inbitwidth = if let Some((ibw, loc)) = inbitwidth {
            if ibw != map.inputsize() {
                let msg = "Declared input address width doesn't match the size of the map.";
                let hint = format!("Set this value to {}", map.inputsize());
                let err = VelosiAstErrBuilder::warn(msg.to_string())
                    .add_location(loc)
                    .add_hint(hint)
                    .build();
                issues.push(err);
                map.inputsize()
            } else {
                ibw
            }
        } else {
            map.inputsize()
        };

        let outbitwidth = if let Some((obw, _loc)) = outbitwidth {
            obw
        } else {
            let msg = "Unit has no output bitwidth definition. Assuming 64 bits.";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            64
        };

        let res = Self {
            ident: VelosiAstIdentifier::from(pt.name),
            params,
            derived,
            inbitwidth,
            outbitwidth,
            consts,
            consts_map,
            methods,
            methods_map,
            map,
            loc: pt.loc,
        };

        // and restore the context again.
        st.drop_context();

        ast_result_return!(VelosiAstUnit::StaticMap(Rc::new(res)), issues)
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

    pub fn get_method(&self, name: &str) -> Option<&Rc<VelosiAstMethod>> {
        self.methods_map.get(name)
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
}

/// Implementation of [Display] for [VelosiAstUnitStaticMap]
impl Display for VelosiAstUnitStaticMap {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "staticmap {} (", self.ident)?;
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            Display::fmt(p, f)?;
        }
        write!(f, ")")?;
        if let Some(d) = &self.derived {
            write!(f, " : {}", d)?;
        }
        writeln!(f, " {{")?;

        for c in &self.consts {
            write!(f, "  ")?;
            Display::fmt(c, f)?;
            writeln!(f)?;
        }

        if self.consts.is_empty() {
            writeln!(f, "  // no constants")?;
        }
        writeln!(f)?;

        writeln!(f, "  inbitwidth = {};", self.inbitwidth)?;
        writeln!(f, "  outbitwidth = {};\n", self.outbitwidth)?;

        for (i, m) in self.methods.iter().enumerate() {
            if i > 0 {
                writeln!(f, "\n")?;
            }
            Display::fmt(m, f)?;
        }

        if self.methods.is_empty() {
            write!(f, "  // no methods")?;
        }

        write!(f, "\n  mapdef = ")?;
        Display::fmt(&self.map, f)?;
        write!(f, ";")?;

        write!(f, "\n}}")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiAstUnit {
    Segment(Rc<VelosiAstUnitSegment>),
    StaticMap(Rc<VelosiAstUnitStaticMap>),
}

impl VelosiAstUnit {
    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeUnit,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        use VelosiParseTreeUnit::*;
        match pt {
            Segment(pt) => VelosiAstUnitSegment::from_parse_tree(pt, st),
            StaticMap(pt) => VelosiAstUnitStaticMap::from_parse_tree(pt, st),
        }
    }

    /// obtains a reference to the identifier
    pub fn ident(&self) -> &Rc<String> {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.ident(),
            StaticMap(s) => s.ident(),
        }
    }

    /// obtains a copy of the identifer
    pub fn ident_to_string(&self) -> String {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.ident_to_string(),
            StaticMap(s) => s.ident_to_string(),
        }
    }

    /// obtains a reference to the fully qualified path
    pub fn path(&self) -> &Rc<String> {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.path(),
            StaticMap(s) => s.path(),
        }
    }

    /// obtains a copy of the fully qualified path
    pub fn path_to_string(&self) -> String {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.path_to_string(),
            StaticMap(s) => s.path_to_string(),
        }
    }

    pub fn params_as_slice(&self) -> &[Rc<VelosiAstParam>] {
        use VelosiAstUnit::*;
        match self {
            Segment(pt) => pt.params_as_slice(),
            StaticMap(pt) => pt.params_as_slice(),
        }
    }

    pub fn input_bitwidth(&self) -> u64 {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.inbitwidth,
            StaticMap(s) => s.inbitwidth,
        }
    }

    pub fn vaddr_max(&self) -> u64 {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.vaddr_max(),
            Segment(segment) => segment.vaddr_max(),
        }
    }

    pub fn paddr_max(&self) -> u64 {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.paddr_max(),
            Segment(segment) => segment.paddr_max(),
        }
    }

    pub fn methods(&self) -> &[Rc<VelosiAstMethod>] {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.methods.as_slice(),
            Segment(segment) => segment.methods.as_slice(),
        }
    }

    pub fn get_method(&self, name: &str) -> Option<&Rc<VelosiAstMethod>> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.get_method(name),
            Segment(segment) => segment.get_method(name),
        }
    }

    pub fn consts(&self) -> &[Rc<VelosiAstConst>] {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.consts.as_slice(),
            Segment(segment) => segment.consts.as_slice(),
        }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => &s.loc,
            StaticMap(s) => &s.loc,
        }
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<VelosiAstUnit> for Symbol {
    fn from(unit: VelosiAstUnit) -> Self {
        let ti = VelosiAstType::from(unit.clone());
        let name = unit.path().clone();
        Symbol::new(name, ti, VelosiAstNode::Unit(unit))
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<VelosiAstUnit> for VelosiAstType {
    fn from(unit: VelosiAstUnit) -> Self {
        let name = unit.ident().clone();
        VelosiAstType::new(VelosiAstTypeInfo::TypeRef(name), unit.loc().clone())
    }
}

/// Implementation of [Display] for [VelosiAstUnit]
impl Display for VelosiAstUnit {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiAstUnit::Segment(s) => Display::fmt(s, f),
            VelosiAstUnit::StaticMap(s) => Display::fmt(s, f),
        }
    }
}
