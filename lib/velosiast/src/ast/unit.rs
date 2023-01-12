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
    VelosiAstStaticMap, VelosiOperation,
};
use crate::error::{
    VelosiAstErrBuilder, VelosiAstErrDoubleDef, VelosiAstErrUndef, VelosiAstIssues,
};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

use super::flags::VelosiAstFlags;
use super::{VelosiAstIdentifier, VelosiAstState};

macro_rules! ignored_node (
    ($node:path, $pst:expr, $issues:expr, $kind:expr) => {
       {
            let msg = format!("Ignored unit node: {} definitions are not supported in {}.",
            stringify!($node), $kind);
            let hint = "Remove this definition.";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint.to_string())
                .add_location($pst.loc().clone())
                .build();
            $issues.push(err);
        }
    }
);

#[derive(PartialEq, Eq, Clone, Debug)]
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
    pub consts: Vec<Rc<VelosiAstConst>>,
    pub consts_map: HashMap<String, Rc<VelosiAstConst>>,

    pub flags: Option<Rc<VelosiAstFlags>>,

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
                issues.push(*e);
            } else {
                params.push(param);
            }
        }

        let mut methods_map = HashMap::new();
        let mut consts_map = HashMap::new();
        let mut consts = Vec::new();

        let mut inbitwidth = None;
        let mut derived_inbitwidth = None;
        let mut outbitwidth = None;
        let mut derived_outbitwidth = None;

        let mut flags: Option<Rc<VelosiAstFlags>> = None;
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

        // TODO: handle the drivation...
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
                consts.push(c.clone());
                consts_map.insert(c.ident_to_string(), c.clone());
            }

            // merge all the methods, we'll deal with overwriting abstract ones later
            for m in unit.methods() {
                methods_map.insert(m.ident_to_string(), m.clone());
            }

            derived_inbitwidth = Some(unit.input_bitwidth());
            inbitwidth = Some((unit.input_bitwidth(), unit.loc().clone()));

            derived_outbitwidth = Some(unit.output_bitwidth());
            outbitwidth = Some((unit.output_bitwidth(), unit.loc().clone()));

            derived_flags = unit.flags();
            flags = unit.flags();

            // TODO: add to the symbol table!

            derived_interface = unit.interface();
            interface = unit.interface();

            // TODO: add to the symbol table!

            derived_state = unit.state();
            state = unit.state();

            println!("DERIVATION OF Flags\n");
        }

        // add the elements to the symbol table

        consts_map.values().for_each(|c| {
            st.insert(c.clone().into())
                .expect("could not insert into symbol table")
        });

        methods_map.values().for_each(|c| {
            st.insert(c.clone().into())
                .expect("could not insert into symbol table")
        });

        if let Some(f) = &flags {
            st.insert(f.clone().into())
                .expect("could not insert into symbol table")
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
                        consts.push(c.clone());
                        consts_map.insert(c.ident_to_string(), c);
                    }
                }
                VelosiParseTreeUnitNode::InBitWidth(w, loc) => {
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
                VelosiParseTreeUnitNode::OutBitWidth(w, loc) => {
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
                        st.update(flgs.clone().into())
                            .expect("flags already exist n symbol table?");
                        flags = Some(flgs);
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
                            println!("derive state\n");
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
                            println!("derive interface\n");
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

                    // TODO: update the method if it's abstract!

                    println!("TODO: update the method if it's abstract!");

                    if let Err(e) = st.insert(m.clone().into()) {
                        issues.push(*e);
                    } else {
                        methods_map.insert(m.ident_to_string(), m);
                    }
                }
                VelosiParseTreeUnitNode::EnumEntry(f) => ignored_node!(
                    VelosiParseTreeUnitNode::EnumEntry,
                    f,
                    &mut issues,
                    "Segments"
                ),
                VelosiParseTreeUnitNode::Map(f) => {
                    ignored_node!(VelosiParseTreeUnitNode::Map, f, &mut issues, "Segments")
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

        if !methods_map.contains_key("map") && !pt.is_abstract {
            let msg = "Segment unit has no `map` method defined. Using default implementation";
            let hint = format!("add method with signature `{}` to unit", FN_SIG_MAP);
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_map());
            methods_map.insert(m.ident_to_string(), m);
        }

        if !methods_map.contains_key("unmap") && !pt.is_abstract {
            let msg = "Segment unit has no `unmap` method defined. Using default implementation";
            let hint = format!("add method with signature `{}` to unit", FN_SIG_UNMAP);
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_unmap());
            methods_map.insert(m.ident_to_string(), m);
        }

        if !methods_map.contains_key("protect") && !pt.is_abstract {
            let msg = "Segment unit has no `protect` method defined. Using default implementation";
            let hint = format!("add method with signature `{}` to unit", FN_SIG_PROTECT);
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_protect());
            methods_map.insert(m.ident_to_string(), m);
        }

        if !methods_map.contains_key("translate") && !pt.is_abstract {
            let msg = "Segment unit has no `protect` method defined. Using default implementation";
            let hint = format!("add method with signature `{}` to unit", FN_SIG_TRANSLATE);
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_translate());
            methods_map.insert(m.ident_to_string(), m);
        }

        if !methods_map.contains_key("matchflags") && !pt.is_abstract {
            let msg = "Segment unit has no `protect` method defined. Using default implementation";
            let hint = format!("add method with signature `{}` to unit", FN_SIG_MATCHFLAGS);
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint)
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);

            let m = Rc::new(VelosiAstMethod::default_matchflags());
            methods_map.insert(m.ident_to_string(), m);
        }

        // check the methods whether they are still abstract
        if !pt.is_abstract {
            for m in methods_map.values() {
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

            Rc::new(VelosiAstInterface::NoneInterface(pt.loc.clone()))
        };

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

        let res = Self {
            ident: VelosiAstIdentifier::from(pt.name),
            is_abstract: pt.is_abstract,
            params,
            derived,
            inbitwidth,
            outbitwidth,
            state,
            interface,
            consts,
            consts_map,
            flags,
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

    pub fn methods(&self) -> Box<dyn Iterator<Item = &Rc<VelosiAstMethod>> + '_> {
        Box::new(self.methods_map.values())
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
        if let Some(m) = self.methods_map.get_mut(method) {
            if let Some(m) = Rc::get_mut(m) {
                m.ops = ops;
                return;
            }

            if Rc::strong_count(m) > 1 {
                println!(
                    "Method `{}` has > 1 strong references ({})",
                    method,
                    Rc::strong_count(m)
                );
            }
            if Rc::weak_count(m) > 1 {
                println!(
                    "Method `{}` has > 1 weak references ({})",
                    method,
                    Rc::weak_count(m)
                );
            }
        } else {
            unreachable!("method {} not found", method);
        }
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

        for (i, m) in self.methods().enumerate() {
            if i > 0 {
                writeln!(f, "\n")?;
            }
            Display::fmt(m, f)?;
        }

        if self.methods_map.is_empty() {
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
                issues.push(*e);
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
                        issues.push(*e);
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
                VelosiParseTreeUnitNode::Method(method) => {
                    let m = Rc::new(ast_result_unwrap!(
                        VelosiAstMethod::from_parse_tree(method, st),
                        issues
                    ));
                    if let Err(e) = st.insert(m.clone().into()) {
                        issues.push(*e);
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
                VelosiParseTreeUnitNode::Flags(f) => {
                    ignored_node!(VelosiParseTreeUnitNode::Flags, f, &mut issues, "StaticMap")
                }
                VelosiParseTreeUnitNode::State(f) => {
                    ignored_node!(VelosiParseTreeUnitNode::State, f, &mut issues, "StaticMap")
                }
                VelosiParseTreeUnitNode::Interface(f) => ignored_node!(
                    VelosiParseTreeUnitNode::Interface,
                    f,
                    &mut issues,
                    "StaticMap"
                ),
                VelosiParseTreeUnitNode::EnumEntry(f) => ignored_node!(
                    VelosiParseTreeUnitNode::EnumEntry,
                    f,
                    &mut issues,
                    "StaticMap"
                ),
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

        if pt.is_abstract {
            let msg = "StaticMap unit declared as abstract.";
            let hint = "Remove the `abstract` abstract modifiere.";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(pt.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);
        }

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

    pub fn get_unit_names(&self) -> Vec<&str> {
        self.map.get_unit_names()
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
pub struct VelosiAstUnitEnum {
    /// the name of the unit
    pub ident: VelosiAstIdentifier,
    /// the parameters of the unit
    pub params: Vec<Rc<VelosiAstParam>>,

    pub inbitwidth: u64,
    pub outbitwidth: u64,

    pub enums: Vec<(VelosiAstIdentifier, Vec<VelosiAstIdentifier>)>,

    /// the location of the type clause
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
        for p in pt.params.into_iter() {
            let param = Rc::new(ast_result_unwrap!(
                VelosiAstParam::from_parse_tree(p, false, st),
                issues
            ));

            // add the param to the symbol table, if it doesn't exist already
            if let Err(e) = st.insert(param.clone().into()) {
                issues.push(*e);
            } else {
                params.push(param);
            }
        }

        // TODO: handle the drivation...

        let mut enums = Vec::new();
        let mut inbitwidth = 0;
        let outbitwidth = 0;
        for node in pt.nodes.into_iter() {
            match node {
                VelosiParseTreeUnitNode::EnumEntry(e) => {
                    // covert the identifiers..
                    let ident = VelosiAstIdentifier::from(e.ident);

                    let args: Vec<VelosiAstIdentifier> = e
                        .params
                        .into_iter()
                        .map(|p| {
                            let id = VelosiAstIdentifier::from(p);
                            utils::check_param_exists(&mut issues, st, &id);
                            id
                        })
                        .collect();

                    if let Some(sym) = st.lookup(ident.ident()) {
                        if let VelosiAstNode::Unit(u) = &sym.ast_node {
                            if let VelosiAstUnit::Enum(e) = u {
                                let msg = format!(
                                    "unit `{}` is an enum. nested enums are not supported",
                                    ident
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
                                    "unit `{}` has a different inbitwidth to the enum",
                                    ident
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

                                if let Some(s) = st.lookup(arg.ident()) {
                                    if let VelosiAstNode::Param(p) = &s.ast_node {
                                        // there is a unit with that type, so we're good
                                        if !param.ptype.typeinfo.compatible(&p.ptype.typeinfo) {
                                            let msg = "mismatched types";
                                            let hint = format!(
                                                "expected {}, found {}",
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

                    enums.push((ident, args));
                }
                VelosiParseTreeUnitNode::Const(c) => {
                    ignored_node!(VelosiParseTreeUnitNode::Const, c, &mut issues, "Enum")
                }
                VelosiParseTreeUnitNode::InBitWidth(_, _) => todo!(),
                VelosiParseTreeUnitNode::OutBitWidth(_, _) => todo!(),
                VelosiParseTreeUnitNode::Flags(f) => {
                    ignored_node!(VelosiParseTreeUnitNode::Flags, f, &mut issues, "Enum")
                }
                VelosiParseTreeUnitNode::State(pst) => {
                    ignored_node!(VelosiParseTreeUnitNode::State, pst, &mut issues, "Enum")
                }
                VelosiParseTreeUnitNode::Interface(pst) => {
                    ignored_node!(VelosiParseTreeUnitNode::Interface, pst, &mut issues, "Enum")
                }
                VelosiParseTreeUnitNode::Method(m) => {
                    ignored_node!(VelosiParseTreeUnitNode::Method, m, &mut issues, "Enum")
                }
                VelosiParseTreeUnitNode::Map(m) => {
                    ignored_node!(VelosiParseTreeUnitNode::Map, m, &mut issues, "Enum")
                }
            }
        }

        let res = Self {
            ident: VelosiAstIdentifier::from(pt.name),
            params,
            inbitwidth,
            outbitwidth,
            enums,
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

    pub fn get_unit_names(&self) -> Vec<&str> {
        self.enums.iter().map(|(ident, _)| ident.as_str()).collect()
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

        writeln!(f, "  inbitwidth = {};", self.inbitwidth)?;
        writeln!(f, "  outbitwidth = {};\n", self.outbitwidth)?;

        for (e, p) in &self.enums {
            write!(f, "  {}(", e)?;
            for (i, p) in p.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", p)?;
            }
            writeln!(f, "  ),")?;
        }

        write!(f, "\n}}")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiAstUnit {
    Segment(Rc<VelosiAstUnitSegment>),
    StaticMap(Rc<VelosiAstUnitStaticMap>),
    Enum(Rc<VelosiAstUnitEnum>),
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
            Enum(pt) => VelosiAstUnitEnum::from_parse_tree(pt, st),
        }
    }

    /// obtains a reference to the identifier
    pub fn ident(&self) -> &Rc<String> {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.ident(),
            StaticMap(s) => s.ident(),
            Enum(e) => e.ident(),
        }
    }

    /// obtains a copy of the identifer
    pub fn ident_to_string(&self) -> String {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.ident_to_string(),
            StaticMap(s) => s.ident_to_string(),
            Enum(e) => e.ident_to_string(),
        }
    }

    /// obtains a reference to the fully qualified path
    pub fn path(&self) -> &Rc<String> {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.path(),
            StaticMap(s) => s.path(),
            Enum(e) => e.path(),
        }
    }

    /// obtains a copy of the fully qualified path
    pub fn path_to_string(&self) -> String {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.path_to_string(),
            StaticMap(s) => s.path_to_string(),
            Enum(e) => e.path_to_string(),
        }
    }

    /// whether the unit is abstract or conceret
    pub fn is_abstract(&self) -> bool {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.is_abstract,
            StaticMap(_) => false,
            Enum(_) => false,
        }
    }

    pub fn is_segment(&self) -> bool {
        matches!(self, VelosiAstUnit::Segment(_))
    }

    pub fn is_staticmap(&self) -> bool {
        matches!(self, VelosiAstUnit::StaticMap(_))
    }

    pub fn is_enum(&self) -> bool {
        matches!(self, VelosiAstUnit::Enum(_))
    }

    pub fn params_as_slice(&self) -> &[Rc<VelosiAstParam>] {
        use VelosiAstUnit::*;
        match self {
            Segment(pt) => pt.params_as_slice(),
            StaticMap(pt) => pt.params_as_slice(),
            Enum(pt) => pt.params_as_slice(),
        }
    }

    pub fn input_bitwidth(&self) -> u64 {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.inbitwidth,
            StaticMap(s) => s.inbitwidth,
            Enum(e) => e.inbitwidth,
        }
    }

    pub fn output_bitwidth(&self) -> u64 {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => s.outbitwidth,
            StaticMap(s) => s.outbitwidth,
            Enum(e) => e.outbitwidth,
        }
    }

    pub fn vaddr_max(&self) -> u64 {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.vaddr_max(),
            Segment(segment) => segment.vaddr_max(),
            Enum(e) => e.vaddr_max(),
        }
    }

    pub fn paddr_max(&self) -> u64 {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.paddr_max(),
            Segment(segment) => segment.paddr_max(),
            Enum(e) => e.paddr_max(),
        }
    }

    pub fn methods(&self) -> Box<dyn Iterator<Item = &Rc<VelosiAstMethod>> + '_> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => Box::new(staticmap.methods.iter()),
            Segment(segment) => Box::new(segment.methods()),
            Enum(_) => Box::new(std::iter::empty()),
        }
    }

    pub fn get_method(&self, name: &str) -> Option<&Rc<VelosiAstMethod>> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.get_method(name),
            Segment(segment) => segment.get_method(name),
            Enum(_) => None,
        }
    }

    pub fn consts(&self) -> &[Rc<VelosiAstConst>] {
        use VelosiAstUnit::*;
        match self {
            StaticMap(staticmap) => staticmap.consts.as_slice(),
            Segment(segment) => segment.consts.as_slice(),
            Enum(_) => &[],
        }
    }

    pub fn flags(&self) -> Option<Rc<VelosiAstFlags>> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(_) => None,
            Segment(segment) => segment.flags.clone(),
            Enum(_) => None,
        }
    }

    pub fn interface(&self) -> Option<Rc<VelosiAstInterface>> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(_) => None,
            Segment(segment) => {
                if !segment.interface.is_none() {
                    Some(segment.interface.clone())
                } else {
                    None
                }
            }
            Enum(_) => None,
        }
    }

    pub fn state(&self) -> Option<Rc<VelosiAstState>> {
        use VelosiAstUnit::*;
        match self {
            StaticMap(_) => None,
            Segment(segment) => {
                if !segment.state.is_none_state() {
                    Some(segment.state.clone())
                } else {
                    None
                }
            }
            Enum(_) => None,
        }
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        use VelosiAstUnit::*;
        match self {
            Segment(s) => &s.loc,
            StaticMap(s) => &s.loc,
            Enum(e) => &e.loc,
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
            VelosiAstUnit::Enum(e) => Display::fmt(e, f),
        }
    }
}
