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
use indexmap::{
    map::{Values, ValuesMut},
    IndexMap,
};

// used parse tree definitions
use velosiparser::{VelosiParseTreeUnitDef, VelosiParseTreeUnitNode, VelosiTokenStream};

// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstErrDoubleDef, VelosiAstIssues};
use crate::{
    ast_result_return, ast_result_unwrap, unit_ignore_node, utils, AstResult, SymbolTable,
};

use crate::ast::{
    VelosiAstConst, VelosiAstExpr, VelosiAstIdentifier, VelosiAstMethod, VelosiAstParam,
    VelosiAstStaticMap, VelosiAstUnit,
};

#[derive(PartialEq, Eq, Clone)]
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
    pub consts: IndexMap<String, Rc<VelosiAstConst>>,

    pub methods: IndexMap<String, Rc<VelosiAstMethod>>,

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

        let derived = if let Some(d) = pt.derived {
            let d = VelosiAstIdentifier::from(d);
            utils::check_type_exists(&mut issues, st, &d);
            Some(Rc::new(d))
        } else {
            None
        };

        // TODO: handle the drivation...

        let mut methods = IndexMap::new();
        let mut consts = IndexMap::new();
        let mut inbitwidth: Option<(u64, VelosiTokenStream)> = None;
        let mut outbitwidth: Option<(u64, VelosiTokenStream)> = None;
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
                    if inbitwidth.is_some() {
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
                    if outbitwidth.is_some() {
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
                VelosiParseTreeUnitNode::Method(method) => {
                    let m = Rc::new(ast_result_unwrap!(
                        VelosiAstMethod::from_parse_tree(method, st),
                        issues
                    ));
                    if let Err(e) = st.insert(m.clone().into()) {
                        issues.push(*e);
                    } else {
                        methods.insert(m.ident_to_string(), m);
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
                    unit_ignore_node!(VelosiParseTreeUnitNode::Flags, f, &mut issues, "StaticMap")
                }
                VelosiParseTreeUnitNode::State(f) => {
                    unit_ignore_node!(VelosiParseTreeUnitNode::State, f, &mut issues, "StaticMap")
                }
                VelosiParseTreeUnitNode::Interface(f) => unit_ignore_node!(
                    VelosiParseTreeUnitNode::Interface,
                    f,
                    &mut issues,
                    "StaticMap"
                ),
                VelosiParseTreeUnitNode::EnumEntry(f) => unit_ignore_node!(
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
            // XXX: not sure if output bitwidth actually makes sense for static maps
            // let msg = "Unit has no output bitwidth definition. Assuming 64 bits.";
            // let err = VelosiAstErrBuilder::warn(msg.to_string())
            //     .add_location(pt.loc.from_self_with_subrange(0..1))
            //     .build();
            // issues.push(err);

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

        if !methods.contains_key("map") {
            methods.insert("map".to_string(), Rc::new(VelosiAstMethod::default_map()));
        }

        if !methods.contains_key("unmap") {
            methods.insert(
                "unmap".to_string(),
                Rc::new(VelosiAstMethod::default_unmap()),
            );
        }

        if !methods.contains_key("protect") {
            methods.insert(
                "protect".to_string(),
                Rc::new(VelosiAstMethod::default_protect()),
            );
        }

        let res = Self {
            ident: VelosiAstIdentifier::from(pt.name),
            params,
            derived,
            inbitwidth,
            outbitwidth,
            consts,
            methods,
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
            write!(f, " : {d}")?;
        }
        writeln!(f, " {{")?;

        for c in self.consts.values() {
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

        for (i, m) in self.methods.values().enumerate() {
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

/// Implementation of [Debug] for [VelosiAstUnitStaticMap]
impl Debug for VelosiAstUnitStaticMap {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
