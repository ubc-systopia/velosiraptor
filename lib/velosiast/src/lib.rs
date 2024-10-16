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

use std::fmt::{Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use indexmap::map::{Keys, Values, ValuesMut};

use ast::VelosiAstFlags;
// public re-exports
pub use velosiparser::{VelosiParser, VelosiParserError, VelosiTokenStream};

// crate modules
pub mod ast;
mod error;
mod symboltable;
mod utils;

use error::VelosiAstErrBuilder;
pub use error::VelosiAstIssues;
pub use symboltable::{Symbol, SymbolTable};
use velosiparser::parsetree::VelosiParseTree;

pub use crate::ast::{
    VelosiAstConst, VelosiAstField, VelosiAstFieldSlice, VelosiAstInterface,
    VelosiAstInterfaceField, VelosiAstInterfaceMemoryField, VelosiAstInterfaceMmioField,
    VelosiAstInterfaceRegisterField, VelosiAstMethod, VelosiAstMethodProperty, VelosiAstRoot,
    VelosiAstStateField, VelosiAstStaticMap, VelosiAstStaticMapElement, VelosiAstStaticMapExplicit,
    VelosiAstStaticMapListComp, VelosiAstTypeInfo, VelosiAstTypeProperty, VelosiAstUnit,
    VelosiAstUnitEnum, VelosiAstUnitOSSpec, VelosiAstUnitProperty, VelosiAstUnitSegment,
    VelosiAstUnitStaticMap,
};

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

#[derive(PartialEq, Eq, Clone, Debug, Default)]
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

    fn validate_os_spec(
        ast: AstResult<VelosiAst, VelosiAstIssues>,
    ) -> AstResult<VelosiAst, VelosiAstIssues> {
        let (ast, mut issues) = match ast {
            AstResult::Ok(ast) => (ast, VelosiAstIssues::new()),
            AstResult::Issues(ast, err) => (ast, err),
            AstResult::Err(err) => return AstResult::Err(err),
        };

        match ast
            .root
            .units()
            .filter(|u| matches!(u, VelosiAstUnit::OSSpec(_)))
            .count()
        {
            1 => (), // all ok, we expect one unit here
            n => {
                let message = format!("Expected a single OS specification, but found {n}");
                let err = VelosiAstErrBuilder::err(message).build();
                issues.push(err);
            }
        }

        ast_result_return!(ast, issues)
    }

    pub fn osspec_from_string(content: String) -> AstResult<VelosiAst, VelosiAstIssues> {
        let ast = Self::from_string(content);
        Self::validate_os_spec(ast)
    }

    pub fn osspec_from_file(filename: &str) -> AstResult<VelosiAst, VelosiAstIssues> {
        let ast = Self::from_file(filename);
        Self::validate_os_spec(ast)
    }

    pub fn consts(&self) -> Values<String, Rc<VelosiAstConst>> {
        self.root.consts()
    }

    pub fn consts_idents(&self) -> Keys<String, Rc<VelosiAstConst>> {
        self.root.consts_idents()
    }

    pub fn consts_mut(&mut self) -> ValuesMut<String, Rc<VelosiAstConst>> {
        self.root.consts_mut()
    }

    pub fn get_const(&self, ident: &str) -> Option<&VelosiAstConst> {
        self.root.get_const(ident)
    }

    pub fn get_const_mut(&mut self, ident: &str) -> Option<&mut VelosiAstConst> {
        self.root.get_const_mut(ident)
    }

    pub fn units(&self) -> Values<String, VelosiAstUnit> {
        self.root.units()
    }

    pub fn units_mut(&mut self) -> ValuesMut<String, VelosiAstUnit> {
        self.root.units_mut()
    }

    pub fn units_idents(&self) -> Keys<String, VelosiAstUnit> {
        self.root.units_idents()
    }

    pub fn get_unit(&self, ident: &str) -> Option<&VelosiAstUnit> {
        self.root.get_unit(ident)
    }

    pub fn get_unit_mut(&mut self, ident: &str) -> Option<&mut VelosiAstUnit> {
        self.root.get_unit_mut(ident)
    }

    pub fn osspec(&self) -> Option<&VelosiAstUnitOSSpec> {
        self.root.osspec()
    }

    pub fn segments(&self) -> Vec<&VelosiAstUnitSegment> {
        self.root.segments()
    }

    pub fn staticmaps(&self) -> Vec<&VelosiAstUnitStaticMap> {
        self.root.staticmaps()
    }

    pub fn enums(&self) -> Vec<&VelosiAstUnitEnum> {
        self.root.enums()
    }

    pub fn get_state_registers(&self) -> Vec<Rc<VelosiAstStateField>> {
        self.root.get_state_registers()
    }

    pub fn flags(&self) -> Option<&Rc<VelosiAstFlags>> {
        self.root.flags.as_ref()
    }
}

/// Implementation of [Display] for [VelosiAst]
impl Display for VelosiAst {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(&self.root, f)
    }
}
