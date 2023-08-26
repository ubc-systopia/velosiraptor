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

//! # VelosiAst -- Flags Definitions
//!
//! This module defines permission / access flags of a memory access

// used standard library functionality
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeFlags;
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::{VelosiAstErrDoubleDef, VelosiAstIssues};
use crate::{ast_result_return, utils, AstResult, Symbol, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{VelosiAstIdentifier, VelosiAstNode, VelosiAstType, VelosiAstTypeInfo};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Flags Definition
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Eq, Clone)]
pub struct VelosiAstFlags {
    /// vector of defined flags
    pub flags: Vec<Rc<VelosiAstIdentifier>>,
    /// the position in the source tree where this unit is defined
    pub loc: VelosiTokenStream,
}

impl VelosiAstFlags {
    pub fn new(flags: Vec<Rc<VelosiAstIdentifier>>, loc: VelosiTokenStream) -> VelosiAstFlags {
        VelosiAstFlags { flags, loc }
    }

    pub fn derive_from(&mut self, other: &Self) {
        for flag in &other.flags {
            if !self.flags.contains(flag) {
                self.flags.push(flag.clone());
            }
        }
    }

    pub fn from_parse_tree(pt: VelosiParseTreeFlags) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // conver the flag identifiers
        let flags: Vec<Rc<VelosiAstIdentifier>> = pt
            .flags
            .into_iter()
            .map(|f| Rc::new(VelosiAstIdentifier::from(f)))
            .collect();

        // hashset for checking double occurances
        let mut flag_map: HashMap<&str, &VelosiAstIdentifier> = HashMap::new();
        for flag in flags.iter() {
            utils::check_snake_case(&mut issues, flag);

            // insert into the symbol table
            if let Some(f) = flag_map.get(flag.as_str()) {
                let err = VelosiAstErrDoubleDef::new(
                    flag.path().clone(),
                    flag.loc.clone(),
                    f.loc.clone(),
                );
                issues.push(err.into());
            } else {
                flag_map.insert(flag.as_str(), flag);
            }
        }

        ast_result_return!(Self::new(flags, pt.loc), issues)
    }

    pub fn populate_symboltable(&self, varname: &str, st: &mut SymbolTable) {
        for flag in &self.flags {
            let name = format!("{}.{}", varname, flag.ident());
            let ti = VelosiAstType::new(VelosiAstTypeInfo::Flags, flag.loc.clone());
            let sym = Symbol::new(Rc::new(name), ti, VelosiAstNode::Flag(flag.clone()));
            st.insert(sym)
                .expect("conflict while building the symbol table");
        }
    }
}

/// Implementation of [PartialEq] for [VelosiAstFlags]
impl PartialEq for VelosiAstFlags {
    fn eq(&self, other: &Self) -> bool {
        self.flags == other.flags
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstFlags>> for Symbol {
    fn from(flags: Rc<VelosiAstFlags>) -> Self {
        let ti = VelosiAstType::new(super::VelosiAstTypeInfo::Flags, flags.loc.clone());
        let name = Rc::new(String::from("flags"));
        Symbol::new(name, ti, VelosiAstNode::Flags(flags))
    }
}

impl Display for VelosiAstFlags {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{{ ")?;
        for (i, flag) in self.flags.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", flag.ident())?;
        }
        write!(f, " }}")
    }
}

/// Implementation of [Debug] for [VelosiAstFlags]
impl Debug for VelosiAstFlags {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
