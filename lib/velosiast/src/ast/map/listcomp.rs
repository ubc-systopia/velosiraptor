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

use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeMapListComp;
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{
    VelosiAstNode, VelosiAstParam, VelosiAstRangeExpr, VelosiAstStaticMap,
    VelosiAstStaticMapElement, VelosiAstTypeInfo, VelosiAstUnitProperty,
};

#[derive(Eq, Clone)]
pub struct VelosiAstStaticMapListComp {
    pub inputsize: u64,
    pub elm: VelosiAstStaticMapElement,
    pub var: Rc<VelosiAstParam>,
    pub range: VelosiAstRangeExpr,
    pub loc: VelosiTokenStream,
    pub properties: HashSet<VelosiAstUnitProperty>,
}

impl VelosiAstStaticMapListComp {
    pub fn new(
        elm: VelosiAstStaticMapElement,
        inputsize: u64,
        var: Rc<VelosiAstParam>,
        range: VelosiAstRangeExpr,
        loc: VelosiTokenStream,
        properties: HashSet<VelosiAstUnitProperty>,
    ) -> Self {
        VelosiAstStaticMapListComp {
            inputsize,
            elm,
            var,
            range,
            loc,
            properties,
        }
    }

    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeMapListComp,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstStaticMap, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // convert the properties
        let mut properties: HashSet<VelosiAstUnitProperty> = HashSet::new();
        for p in pt.properties.into_iter() {
            let loc = p.loc.clone();
            let prop = ast_result_unwrap!(VelosiAstUnitProperty::from_parse_tree(p, st), issues);

            if properties.contains(&prop) {
                let msg = "ignoring double defined property";
                let hint = "remove the duplicate property";
                let err = VelosiAstErrBuilder::warn(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(loc)
                    .build();

                issues.push(err);
            } else {
                properties.insert(prop);
            }
        }

        // create the symbol table context
        st.create_context("staticmap".to_string());

        // convert the identifer and check for format
        let var = Rc::new(ast_result_unwrap!(
            VelosiAstParam::from_parse_tree_ident(pt.var, VelosiAstTypeInfo::Integer, st),
            issues
        ));

        // add the ident to the symbol table
        st.insert(var.clone().into())
            .map_err(|e| issues.push(*e))
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
            let msg = format!("Range has not a power of two size ({num})");
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
                    let msg = format!("Inputbitwidth of {inputbits} exceeds maximum of 64 bits");
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

        let res = Self::new(elm, inputbits, var, range, pt.loc, properties);
        ast_result_return!(VelosiAstStaticMap::ListComp(res), issues)
    }

    pub fn get_next_unit_idents(&self) -> Vec<&Rc<String>> {
        vec![self.elm.dst.ident()]
    }

    pub fn is_repr_list(&self) -> bool {
        self.properties.contains(&VelosiAstUnitProperty::ListRepr)
    }
}

/// Implementation of [PartialEq] for [VelosiAstStaticMapListComp]
impl PartialEq for VelosiAstStaticMapListComp {
    fn eq(&self, other: &Self) -> bool {
        self.inputsize == other.inputsize
            && self.elm == other.elm
            && self.var == other.var
            && self.range == other.range
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

/// Implementation of [Debug] for [VelosiAstStaticMap]
impl Debug for VelosiAstStaticMapListComp {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
