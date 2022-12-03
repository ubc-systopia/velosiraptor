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

//! # VelosiAst -- Static Map Definitions
//!
//! This module defines the Constant AST nodes of the langauge

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use velosiparser::{
    VelosiParseTreeMap, VelosiParseTreeMapElement, VelosiParseTreeMapExplicit,
    VelosiParseTreeMapListComp, VelosiTokenStream,
};

use crate::ast::{
    expr::{VelosiAstExpr, VelosiAstFnCallExpr, VelosiAstRangeExpr},
    types::VelosiAstTypeInfo,
    VelosiAstConst, VelosiAstNode, VelosiAstParam,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, SymbolTable};

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiAstStaticMap {
    ListComp(VelosiAstStaticMapListComp),
    Explicit(VelosiAstStaticMapExplicit),
    None(VelosiTokenStream),
}

impl VelosiAstStaticMap {
    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeMap,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        use VelosiParseTreeMap::*;
        match pt {
            ListComp(pt) => VelosiAstStaticMapListComp::from_parse_tree(*pt, st),
            Explicit(pt) => VelosiAstStaticMapExplicit::from_parse_tree(*pt, st),
        }
    }

    pub fn name(&self) -> &str {
        "staticmap"
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        match self {
            VelosiAstStaticMap::ListComp(s) => &s.loc,
            VelosiAstStaticMap::Explicit(s) => &s.loc,
            VelosiAstStaticMap::None(s) => s,
        }
    }

    pub fn inputsize(&self) -> u64 {
        match self {
            VelosiAstStaticMap::ListComp(s) => s.inputsize,
            VelosiAstStaticMap::Explicit(s) => s.inputsize,
            VelosiAstStaticMap::None(_) => 0,
        }
    }

    pub fn get_unit_names(&self) -> Vec<&str> {
        match self {
            VelosiAstStaticMap::ListComp(s) => s.get_unit_names(),
            VelosiAstStaticMap::Explicit(s) => s.get_unit_names(),
            VelosiAstStaticMap::None(_) => vec![],
        }
    }
}

/// Implementation of [Display] for [VelosiAstStaticMap]
impl Display for VelosiAstStaticMap {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiAstStaticMap::ListComp(s) => Display::fmt(s, f),
            VelosiAstStaticMap::Explicit(s) => Display::fmt(s, f),
            VelosiAstStaticMap::None(_) => write!(f, "NoneMap"),
        }
    }
}

impl Default for VelosiAstStaticMap {
    fn default() -> Self {
        VelosiAstStaticMap::None(VelosiTokenStream::default())
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstStaticMapListComp {
    pub inputsize: u64,
    pub elm: VelosiAstStaticMapElement,
    pub var: Rc<VelosiAstParam>,
    pub range: VelosiAstRangeExpr,
    pub loc: VelosiTokenStream,
}

impl VelosiAstStaticMapListComp {
    pub fn new(
        elm: VelosiAstStaticMapElement,
        inputsize: u64,
        var: Rc<VelosiAstParam>,
        range: VelosiAstRangeExpr,
        loc: VelosiTokenStream,
    ) -> Self {
        VelosiAstStaticMapListComp {
            inputsize,
            elm,
            var,
            range,
            loc,
        }
    }

    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeMapListComp,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstStaticMap, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // create the symbol table context
        st.create_context("staticmap".to_string());

        // convert the identifer and check for format
        let var = Rc::new(ast_result_unwrap!(
            VelosiAstParam::from_parse_tree_ident(pt.var, VelosiAstTypeInfo::Integer, st),
            issues
        ));

        // add the ident to the symbol table
        st.insert(var.clone().into())
            .map_err(|e| issues.push(e))
            .ok();

        let range = ast_result_unwrap!(
            VelosiAstRangeExpr::from_parse_tree_raw(pt.range, st),
            issues
        );

        let elm = ast_result_unwrap!(
            VelosiAstStaticMapElement::from_parse_tree(pt.elm, st),
            issues
        );

        let num = range.end - range.start;

        if (num & (num - 1)) != 0 {
            let msg = format!("Range has not a power of two size ({})", num);
            let hint = "Change the range to be a power of two";
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint.to_string())
                .add_location(range.loc.clone())
                .build();
            issues.push(err);
        }

        let mut numbits = 0;
        while numbits < 64 {
            if (1 << numbits) >= num {
                break;
            }
            numbits += 1;
        }

        let mut elms = Vec::new();
        for i in range.start..range.end {
            elms.push(elm.from_self_with_var_value(st, var.ident(), i))
        }

        // check the elements for overlaps
        utils::check_element_ranges(&mut issues, st, elms.as_slice());

        let mut inputbits = 64;
        if let Some(u) = st.lookup(elm.dst.path()) {
            if let VelosiAstNode::Unit(u) = &u.ast_node {
                inputbits = u.input_bitwidth() + numbits;
                if inputbits >= 64 {
                    let msg = format!("Inputbitwidth of {} exceeds maximum of 64 bits", inputbits);
                    let hint = "reduce the range, or the input bitwidth of the element.";
                    let err = VelosiAstErrBuilder::err(msg)
                        .add_hint(hint.to_string())
                        .add_location(pt.loc.clone())
                        .build();
                    issues.push(err);
                    inputbits = 64;
                }
            }
        }

        // drop the symbol table context here, so we can instanticate the variables
        st.drop_context();

        let res = Self::new(elm, inputbits, var, range, pt.loc);
        ast_result_return!(VelosiAstStaticMap::ListComp(res), issues)
    }

    pub fn get_unit_names(&self) -> Vec<&str> {
        vec![self.elm.dst.ident()]
    }
}

/// Implementation of [Display] for [VelosiAstStaticMapListComp]
impl Display for VelosiAstStaticMapListComp {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "[ ")?;
        Display::fmt(&self.elm, f)?;
        write!(f, " for {} in {}", self.var, self.range)?;
        write!(f, " ]")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstStaticMapExplicit {
    pub inputsize: u64,
    pub entries: Vec<VelosiAstStaticMapElement>,
    pub loc: VelosiTokenStream,
}

impl VelosiAstStaticMapExplicit {
    pub fn new(entries: Vec<VelosiAstStaticMapElement>, loc: VelosiTokenStream) -> Self {
        let inputsize: u64 = 0;
        VelosiAstStaticMapExplicit {
            inputsize,
            entries,
            loc,
        }
    }

    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeMapExplicit,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstStaticMap, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        let mut elems = Vec::new();
        for e in pt.entries {
            let elm = ast_result_unwrap!(VelosiAstStaticMapElement::from_parse_tree(e, st), issues);

            elems.push(elm);
        }

        let res = Self::new(elems, pt.loc);
        ast_result_return!(VelosiAstStaticMap::Explicit(res), issues)
    }

    pub fn get_unit_names(&self) -> Vec<&str> {
        self.entries
            .iter()
            .map(|e| e.dst.ident().as_str())
            .collect::<Vec<_>>()
    }
}

/// Implementation of [Display] for [VelosiAstStaticMapExplicit]
impl Display for VelosiAstStaticMapExplicit {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "explicit comp")
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstStaticMapElement {
    pub src: Option<VelosiAstRangeExpr>,
    pub dst: VelosiAstFnCallExpr,
    pub dst_bitwidth: u64,
    pub offset: Option<VelosiAstExpr>,
    pub loc: VelosiTokenStream,
}

impl VelosiAstStaticMapElement {
    pub fn new(
        src: Option<VelosiAstRangeExpr>,
        dst: VelosiAstFnCallExpr,
        dst_bitwidth: u64,
        offset: Option<VelosiAstExpr>,
        loc: VelosiTokenStream,
    ) -> Self {
        VelosiAstStaticMapElement {
            src,
            dst,
            dst_bitwidth,
            offset,
            loc,
        }
    }

    pub fn from_self_with_var_value(&self, st: &mut SymbolTable, var: &str, val: u64) -> Self {
        // prepare the symbol in the symbol table as a constant
        st.remove(var).expect("couldn't remove the symbol");
        let v = Rc::new(VelosiAstConst::new_int(var, val));
        st.insert(v.into()).expect("couldn't insert the symbol");

        let src = self.src.as_ref().map(|src| src.clone().flatten_raw(st));
        let dst = self.dst.clone().flatten_raw(st);
        let offset = self
            .offset
            .as_ref()
            .map(|offset| offset.clone().flatten(st));

        Self::new(src, dst, self.dst_bitwidth, offset, self.loc.clone())
    }

    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeMapElement,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstStaticMapElement, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        let src = if let Some(src) = pt.src {
            Some(ast_result_unwrap!(
                VelosiAstRangeExpr::from_parse_tree_raw(src, st),
                issues
            ))
        } else {
            None
        };

        let dest = ast_result_unwrap!(VelosiAstFnCallExpr::from_parse_tree_raw(pt.dst, st), issues);

        // get the destnation unit
        let destsym = st.lookup(dest.ident()).unwrap(); // that shouldn't fail
        let bitwidth = if let VelosiAstNode::Unit(u) = &destsym.ast_node {
            u.input_bitwidth()
        } else {
            unreachable!()
        };

        let offset = if let Some(offset) = pt.offset {
            Some(ast_result_unwrap!(
                VelosiAstExpr::from_parse_tree(offset, st),
                issues
            ))
        } else {
            None
        };

        ast_result_return!(Self::new(src, dest, bitwidth, offset, pt.loc), issues)
    }
}

/// Implementation of [Display] for [VelosiAstStaticMapElement]
impl Display for VelosiAstStaticMapElement {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if let Some(src) = &self.src {
            write!(f, "{} -> ", src)?;
        }

        Display::fmt(&self.dst, f)?;
        if let Some(offset) = &self.offset {
            write!(f, " @ {}", offset)?;
        }

        Ok(())
    }
}
