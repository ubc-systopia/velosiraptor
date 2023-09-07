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

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeMapExplicit;
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::VelosiAstIssues;
use crate::{ast_result_return, ast_result_unwrap, AstResult, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{VelosiAstStaticMap, VelosiAstStaticMapElement};

#[derive(Eq, Clone, Debug)]
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

    pub fn get_next_unit_idents(&self) -> Vec<&Rc<String>> {
        self.entries
            .iter()
            .map(|e| e.dst.ident())
            .collect::<Vec<_>>()
    }
}

/// Implementation of [PartialEq] for [VelosiAstStaticMapListComp]
impl PartialEq for VelosiAstStaticMapExplicit {
    fn eq(&self, other: &Self) -> bool {
        self.inputsize == other.inputsize && self.entries == other.entries
    }
}

/// Implementation of [Display] for [VelosiAstStaticMapExplicit]
impl Display for VelosiAstStaticMapExplicit {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "explicit comp")
    }
}
