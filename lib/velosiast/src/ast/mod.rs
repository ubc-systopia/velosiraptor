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

//! # VelosiAst -- The Ast for the Velosiraptor Language
//!
//! This module defines the AST of the langauge

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use std::collections::HashMap;

use velosiparser::{VelosiParseTree, VelosiParseTreeContextNode, VelosiTokenStream};

use crate::error::VelosiAstIssues;
use crate::AstResult;
use crate::SymbolTable;

mod constdef;
mod expr;
mod types;

pub use constdef::VelosiAstConst;
pub use types::{VelosiAstType, VelosiAstTypeInfo};

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiAstNode {
    Unit(usize),
    Const(Rc<VelosiAstConst>),
    Method,
    Param(usize),
}

impl VelosiAstNode {
    pub fn loc(&self) -> &VelosiTokenStream {
        use VelosiAstNode::*;
        match self {
            // Unit(loc) => loc,
            Const(c) => &c.loc,
            // Method => todo!(),
            // Param(loc) => loc,
            _ => {
                panic!("nyi")
            }
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstUnit {
    pub name: Rc<String>,
}

/// Defines the root note of the ast
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstRoot {
    pub consts: HashMap<String, Rc<VelosiAstConst>>,
    pub units: HashMap<String, Rc<VelosiAstUnit>>,
    pub context: String,
}

impl VelosiAstRoot {
    pub fn new(context: String) -> Self {
        Self {
            consts: HashMap::new(),
            units: HashMap::new(),
            context,
        }
    }

    pub fn add_const(&mut self, c: VelosiAstConst) {
        self.consts.insert(c.name.to_string(), Rc::new(c));
    }

    pub fn add_unit(&mut self, u: VelosiAstUnit) {
        self.units.insert(u.name.to_string(), Rc::new(u));
    }

    pub fn from_parse_tree(pt: VelosiParseTree) -> AstResult<VelosiAstRoot, VelosiAstIssues> {
        let mut root = Self::new(pt.context.unwrap_or_else(|| "$buf".to_string()));

        // create the symbol table

        let mut st = SymbolTable::new();
        let mut issues = VelosiAstIssues::new();

        for n in pt.nodes {
            match n {
                VelosiParseTreeContextNode::Const(c) => {
                    let c = match VelosiAstConst::from_parse_tree(c, &mut st) {
                        AstResult::Ok(c) => Some(Rc::new(c)),
                        AstResult::Issues(c, i) => {
                            issues.merge(i);
                            Some(Rc::new(c))
                        }
                        AstResult::Err(i) => {
                            issues.merge(i);
                            None
                        }
                    };
                    if let Some(c) = c {
                        if let Err(e) = st.insert(c.clone().into()) {
                            issues.push(e);
                        } else {
                            root.consts.insert(c.name.to_string(), c);
                        }
                    }
                }
                VelosiParseTreeContextNode::Unit(u) => {
                    panic!("not handled yet");
                }
                VelosiParseTreeContextNode::Import(i) => {
                    panic!("triggered ");
                    //return Err(VelosiAstError::Errors { err: 1, warn: 0 });
                }
            }
        }

        if issues.is_ok() {
            AstResult::Ok(root)
        } else {
            AstResult::Issues(root, issues)
        }
    }
}

/// Implementation of [Display] for [VelosiAstRoot]
impl Display for VelosiAstRoot {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        writeln!(f, "VelosiAst({})", self.context)?;
        writeln!(
            f,
            "--------------------------------------------------------"
        )?;
        writeln!(f, "\nConsts:")?;

        for c in self.consts.values() {
            Display::fmt(c, f)?;
            writeln!(f)?;
        }

        writeln!(f, "\nUnits:")?;

        // for u in self.units.values() {
        //     Display::fmt(u, f)?;
        //     writeln!(f)?;
        // }
        writeln!(
            f,
            "--------------------------------------------------------"
        )
    }
}
