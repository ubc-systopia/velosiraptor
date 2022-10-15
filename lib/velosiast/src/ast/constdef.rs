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

//! # VelosiAst -- Constant Definitions
//!
//! This module defines the Constant AST nodes of the langauge

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use velosiparser::{VelosiParseTreeConstDef, VelosiTokenStream};

use crate::ast::{expr::VelosiAstExpr, types::VelosiAstType, VelosiAstNode};

use crate::error::{VelosiAstErr, VelosiAstIssues};
use crate::{AstResult, Symbol, SymbolTable};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstConst {
    /// the name of the constant
    pub name: Rc<String>,
    /// the type of the constant
    pub ctype: VelosiAstType,
    /// expression representing the value of the constnat
    pub value: VelosiAstExpr,
    /// the location of the import clause
    pub loc: VelosiTokenStream,
}

// ff
macro_rules! ast_result_unwrap (($e: expr, $issues: expr) => (
    match $e {
        AstResult::Ok(t) => t,
        AstResult::Issues(t, e) => {
            $issues.merge(e.into());
            t
        }
        AstResult::Err(e) => return AstResult::Err(e.into()),
    }
));

impl VelosiAstConst {
    pub fn from_parse_tree(
        pt: VelosiParseTreeConstDef,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        let ctype = ast_result_unwrap!(VelosiAstType::from_parse_tree(pt.ctype, st), issues);
        let value = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(pt.value, st), issues);

        let res = Self {
            name: Rc::new(pt.name),
            ctype,
            value,
            loc: pt.loc,
        };

        if issues.is_ok() {
            AstResult::Ok(res)
        } else {
            AstResult::Issues(res, issues)
        }
    }
}

impl From<Rc<VelosiAstConst>> for Symbol {
    fn from(c: Rc<VelosiAstConst>) -> Self {
        let n = VelosiAstNode::Const(c.clone());
        Symbol::new(c.name.clone(), c.ctype.clone(), n)
    }
}

/// Implementation of [Display] for [VelosiAstConst]
impl Display for VelosiAstConst {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "const {} : {} = {};", self.name, self.ctype, self.value)
    }
}
