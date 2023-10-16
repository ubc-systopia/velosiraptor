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
//! This module defines the Constant AST nodes of the language

// used standard library functionality
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeMapElement;
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::VelosiAstIssues;
use crate::{ast_result_return, ast_result_unwrap, AstResult, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{
    VelosiAstConst, VelosiAstExpr, VelosiAstFnCallExpr, VelosiAstNode, VelosiAstRangeExpr,
};

#[derive(Eq, Clone)]
pub struct VelosiAstStaticMapElement {
    pub src: Option<VelosiAstRangeExpr>,
    pub dst: VelosiAstFnCallExpr,
    pub dst_bitwidth: u64,
    pub offset: Option<VelosiAstExpr>,
    pub loc: VelosiTokenStream,
    pub has_memory_state: bool,
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
            has_memory_state: false,
        }
    }

    pub fn from_self_with_var_value(&self, st: &mut SymbolTable, var: &str, val: u64) -> Self {
        // prepare the symbol in the symbol table as a constant
        st.remove(var).expect("couldn't remove the symbol");
        let v = Rc::new(VelosiAstConst::new_int(var, val));
        st.insert(v.into()).expect("couldn't insert the symbol");

        let mapping = HashMap::new();

        let src = self
            .src
            .as_ref()
            .map(|src| src.clone().flatten_raw(st, &mapping));
        let dst = self.dst.clone().flatten_raw(st, &mapping);
        let offset = self
            .offset
            .as_ref()
            .map(|offset| offset.clone().flatten(st, &mapping));

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

        let dst = ast_result_unwrap!(VelosiAstFnCallExpr::from_parse_tree_raw(pt.dst, st), issues);

        // get the destination unit
        let mut has_memory_state = false;
        let bitwidth = if let Some(destsym) = st.lookup(dst.ident()) {
            if let VelosiAstNode::Unit(u) = &destsym.ast_node {
                has_memory_state = u.has_memory_state();
                u.input_bitwidth()
            } else {
                64
            }
        } else {
            64
        };

        let offset = if let Some(offset) = pt.offset {
            Some(ast_result_unwrap!(
                VelosiAstExpr::from_parse_tree(offset, st),
                issues
            ))
        } else {
            None
        };

        ast_result_return!(
            VelosiAstStaticMapElement {
                src,
                dst,
                dst_bitwidth: bitwidth,
                offset,
                loc: pt.loc,
                has_memory_state
            },
            issues
        )
    }

    pub fn has_memory_state(&self) -> bool {
        self.has_memory_state
    }
}

/// Implementation of [PartialEq] for [VelosiAstStaticMapElement]
impl PartialEq for VelosiAstStaticMapElement {
    fn eq(&self, other: &Self) -> bool {
        self.src == other.src
            && self.dst == other.dst
            && self.dst_bitwidth == other.dst_bitwidth
            && self.offset == other.offset
    }
}

/// Implementation of [Display] for [VelosiAstStaticMapElement]
impl Display for VelosiAstStaticMapElement {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if let Some(src) = &self.src {
            write!(f, "{src} -> ")?;
        }

        Display::fmt(&self.dst, f)?;
        if let Some(offset) = &self.offset {
            write!(f, " @ {offset}")?;
        }

        Ok(())
    }
}

/// Implementation of [Debug] for [VelosiAstStaticMapElement]
impl Debug for VelosiAstStaticMapElement {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
