// VelosiParser -- a parser for the Velosiraptor Language
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

//! # VelosiParser -- The Velosiraptor Parser
//!
//! The VelosiParser consumes the lexed TokenStream and produces a parse tree for the
//! for further processing.

// used standard library functionality

use std::collections::HashMap;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use ast::VelosiAstConst;
// public re-exports
pub use velosiparser::{VelosiParser, VelosiParserError, VelosiTokenStream};

// crate modules
pub mod ast;
mod error;
mod symboltable;
mod utils;

use error::{VelosiAstErrBuilder, VelosiAstIssues};
use symboltable::{Symbol, SymbolTable};
use velosiparser::VelosiParseTree;

pub use crate::ast::{VelosiAstRoot, VelosiAstUnit, VelosiAstUnitSegment, VelosiAstUnitStaticMap};

// custom error definitions
pub enum AstResult<T, E> {
    Ok(T),
    Issues(T, E),
    Err(E),
}

#[macro_export]
macro_rules! ast_result_unwrap (($e: expr, $issues: expr) => (
    match $e {
        AstResult::Ok(t) => t,
        AstResult::Issues(t, e) => {
            $issues.merge(e.into());
            t
        }
        AstResult::Err(e) => {
            $issues.merge(e.into());
            return AstResult::Err($issues)
        },
    }
));

#[macro_export]
macro_rules! ast_result_return (($res: expr, $issues: expr) => (
    if $issues.is_ok() {
        AstResult::Ok($res)
    } else {
        AstResult::Issues($res, $issues)
    }
));

/// represents the lexer state

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAst {
    root: VelosiAstRoot,
}

impl VelosiAst {
    pub fn from_parse_tree(ptree: VelosiParseTree) -> AstResult<VelosiAst, VelosiAstIssues> {
        match VelosiAstRoot::from_parse_tree(ptree) {
            AstResult::Ok(root) => AstResult::Ok(VelosiAst { root }),
            AstResult::Issues(root, issues) => {
                if issues.has_errors() {
                    AstResult::Err(issues)
                } else {
                    AstResult::Issues(VelosiAst { root }, issues)
                }
            }
            AstResult::Err(issues) => AstResult::Err(issues),
        }
    }

    fn from_parse_result(
        res: Result<VelosiParseTree, VelosiParserError>,
    ) -> AstResult<VelosiAst, VelosiAstIssues> {
        match res {
            Ok(ptree) => VelosiAst::from_parse_tree(ptree),
            Err(VelosiParserError::ReadSourceFile { e }) => {
                let msg = format!("Failed to read the source file: `{e}`");
                let err = VelosiAstErrBuilder::err(msg).build();
                AstResult::Err(err.into())
            }

            Err(VelosiParserError::ImportFailure { e }) => {
                let msg = format!("Import failure: {e}");
                let err = VelosiAstErrBuilder::err(msg).build();
                AstResult::Err(err.into())
            }

            Err(VelosiParserError::LexingFailure { e }) => {
                let msg = format!("Lexing failure. \n\n{e}");
                let err = VelosiAstErrBuilder::err(msg).build();
                AstResult::Err(err.into())
            }

            Err(VelosiParserError::ParsingFailure { e }) => {
                let msg = format!("Parsing failure. \n\n{e}");
                let err = VelosiAstErrBuilder::err(msg).build();
                AstResult::Err(err.into())
            }
        }
    }

    pub fn from_string(content: String) -> AstResult<VelosiAst, VelosiAstIssues> {
        Self::from_parse_result(VelosiParser::parse_string(content))
    }

    pub fn from_file(filename: &str) -> AstResult<VelosiAst, VelosiAstIssues> {
        Self::from_parse_result(VelosiParser::parse_file(filename, true))
    }

    pub fn consts(&self) -> &[Rc<VelosiAstConst>] {
        self.root.consts()
    }

    pub fn take_segment_unit(&mut self) -> Option<VelosiAstUnitSegment> {
        self.root.take_segment_unit()
    }

    pub fn put_segment_unit(&mut self, unit: VelosiAstUnitSegment) {
        self.root.put_segment_unit(unit)
    }

    pub fn segment_units(&self) -> impl Iterator<Item = &Rc<VelosiAstUnitSegment>> {
        self.root.segments_map.values()
    }

    pub fn segment_units_mut(&mut self) -> impl Iterator<Item = &mut Rc<VelosiAstUnitSegment>> {
        self.root.segments_map.values_mut()
    }

    pub fn staticmap_units(&self) -> impl Iterator<Item = &Rc<VelosiAstUnitStaticMap>> {
        self.root.staticmap_map.values()
    }

    /// get a map of all non-abstract units
    pub fn unit_map(&self) -> HashMap<Rc<String>, VelosiAstUnit> {
        self.root.unit_map()
    }
}

/// Implementation of [Display] for [VelosiAst]
impl Display for VelosiAst {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(&self.root, f)
    }
}
