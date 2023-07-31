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
use std::collections::{HashMap, HashSet};
use std::io::Error;
use std::path::{Path, PathBuf};

// external dependencies
use custom_error::custom_error;

pub use velosilexer::{VelosiLexer, VelosiLexerError, VelosiTokenStream};

use velosilexer::{VelosiKeyword, VelosiOpToken, VelosiTokenKind};

// crate modules
mod error;
mod parser;
mod parsetree;

pub use error::VelosiParserErr;
pub use parsetree::{
    VelosiParseTree, VelosiParseTreeBinOp, VelosiParseTreeBinOpExpr, VelosiParseTreeBoolLiteral,
    VelosiParseTreeConstDef, VelosiParseTreeContextNode, VelosiParseTreeExpr, VelosiParseTreeField,
    VelosiParseTreeFieldSlice, VelosiParseTreeFlags, VelosiParseTreeFnCallExpr,
    VelosiParseTreeIdentifier, VelosiParseTreeIdentifierLiteral, VelosiParseTreeIfElseExpr,
    VelosiParseTreeInterface, VelosiParseTreeInterfaceAction, VelosiParseTreeInterfaceActions,
    VelosiParseTreeInterfaceDef, VelosiParseTreeInterfaceField,
    VelosiParseTreeInterfaceFieldMemory, VelosiParseTreeInterfaceFieldMmio,
    VelosiParseTreeInterfaceFieldNode, VelosiParseTreeInterfaceFieldRegister, VelosiParseTreeMap,
    VelosiParseTreeMapElement, VelosiParseTreeMapExplicit, VelosiParseTreeMapListComp,
    VelosiParseTreeMethod, VelosiParseTreeMethodProperty, VelosiParseTreeNumLiteral,
    VelosiParseTreeParam, VelosiParseTreeQuantifier, VelosiParseTreeQuantifierExpr,
    VelosiParseTreeRangeExpr, VelosiParseTreeSliceExpr, VelosiParseTreeState,
    VelosiParseTreeStateDef, VelosiParseTreeStateField, VelosiParseTreeStateFieldMemory,
    VelosiParseTreeStateFieldRegister, VelosiParseTreeType, VelosiParseTreeTypeInfo,
    VelosiParseTreeUnOp, VelosiParseTreeUnOpExpr, VelosiParseTreeUnit, VelosiParseTreeUnitDef,
    VelosiParseTreeUnitNode,
};

use error::IResult;
use error::VelosiParserErrBuilder;

// // custom error definitions
custom_error! {pub VelosiParserError
    ReadSourceFile {e: Error} = "Could not read the source file.",
    LexingFailure { e: VelosiParserErr }   = "Lexing failed.",
    ParsingFailure { e: VelosiParserErr } = "Parsing failed.",
    ImportFailure { e: VelosiParserErr } = "Import failed.",
}

impl From<VelosiLexerError> for VelosiParserError {
    fn from(err: VelosiLexerError) -> Self {
        match err {
            VelosiLexerError::ReadSourceFile { e } => VelosiParserError::ReadSourceFile { e },
            VelosiLexerError::LexingFailure { r } => {
                VelosiParserError::LexingFailure { e: r.into() }
            }
            VelosiLexerError::LexingIncomplete => {
                let message = "Lexing incomplete: input stream ended unexpectedly.";
                let e = VelosiParserErrBuilder::new(message.to_string()).build();
                VelosiParserError::LexingFailure { e }
            }
        }
    }
}

/// represents the lexer state
pub struct VelosiParser;

impl VelosiParser {
    fn maybe_resolve_imports(
        res: IResult<VelosiTokenStream, VelosiParseTree>,
        resolve_imports: bool,
    ) -> Result<VelosiParseTree, VelosiParserError> {
        match res {
            Ok((_, ptree)) => {
                if resolve_imports {
                    VelosiParser::resolve_imports(ptree)
                } else {
                    Ok(ptree)
                }
            }
            Err(nom::Err::Error(e)) => Err(VelosiParserError::ParsingFailure { e }),
            Err(nom::Err::Failure(e)) => Err(VelosiParserError::ParsingFailure { e }),
            Err(nom::Err::Incomplete(_)) => {
                let message = "Parsing incomplete: input stream ended unexpectedly.";
                let e = VelosiParserErrBuilder::new(message.to_string()).build();
                Err(VelosiParserError::ParsingFailure { e })
            }
        }
    }

    /// Parses the supplied [VelosiTokenStream] and converts it into a [VelosiParseTree]
    ///
    /// This function will create a new `VelosiParseTree` from the supplied string.
    pub fn parse_tokstream(
        tokens: VelosiTokenStream,
        resolve_imports: bool,
    ) -> Result<VelosiParseTree, VelosiParserError> {
        let ts = tokens.with_retained(|t| t.keep());
        VelosiParser::maybe_resolve_imports(parser::parse(ts), resolve_imports)
    }

    /// Parses the supplied [VelosiTokenStream] and converts it into a [VelosiParseTree]
    ///
    /// This function will create a new `VelosiParseTree` from the supplied string.
    pub fn parse_tokstream_with_context(
        tokens: VelosiTokenStream,
        context: String,
        resolve_imports: bool,
    ) -> Result<VelosiParseTree, VelosiParserError> {
        let ts = tokens.with_retained(|t| t.keep());
        VelosiParser::maybe_resolve_imports(
            parser::parse_with_context(ts, context),
            resolve_imports,
        )
    }

    /// Parses the supplied string and converts it into a [VelosiParseTree]
    ///
    /// This function will create a new `VelosiParseTree` from the supplied string.
    pub fn parse_string(content: String) -> Result<VelosiParseTree, VelosiParserError> {
        match VelosiLexer::lex_string(content) {
            Ok(tokens) => {
                VelosiParser::parse_tokstream_with_context(tokens, "$buf".to_string(), false)
            }
            Err(e) => Err(e.into()),
        }
    }

    /// Parses the supplied file and converts it into a [VelosiParseTree]
    pub fn parse_file(
        filename: &str,
        resolve_imports: bool,
    ) -> Result<VelosiParseTree, VelosiParserError> {
        match VelosiLexer::lex_file(filename) {
            Ok(tokens) => VelosiParser::parse_tokstream_with_context(
                tokens,
                filename.to_string(),
                resolve_imports,
            ),

            Err(e) => Err(e.into()),
        }
    }

    /// recursively resolves the imports and produces a tree of parse trees
    fn do_resolve_imports(
        ptree: VelosiParseTree,
        path: &mut Vec<String>,
    ) -> Result<ImportResolver, VelosiParserError> {
        // push ourselves to the sequence of imports, as we recurse later
        if let Some(filename) = &ptree.context {
            path.push(filename.clone());
        } else {
            path.push("$buf".to_string());
        }

        // get the import file, the parent directory of the current one
        let mut importpath = if let Some(c) = &ptree.context {
            match Path::new(&c).parent() {
                Some(d) => PathBuf::from(d),
                None => PathBuf::from("./"),
            }
        } else {
            PathBuf::from("./")
        };

        // resolve the imports
        let mut current_imports: HashMap<String, VelosiTokenStream> = HashMap::new();
        let mut resolved_imports = Vec::new();
        for import in ptree.imports() {
            // just stop when we have a douplicate import, return the error
            match current_imports.get(import.name()) {
                Some(i) => {
                    let msg = format!("Duplicate import `{}`", import.name());
                    let err1 = VelosiParserErrBuilder::new(msg)
                        .add_tokstream(import.loc().clone())
                        .add_hint("Remove this duplicate import.".to_string())
                        .build();

                    let msg = "Previous import was here:";
                    let err2 = VelosiParserErrBuilder::new(msg.to_string())
                        .add_tokstream(i.clone())
                        .build();

                    return Err(VelosiParserError::ImportFailure {
                        e: VelosiParserErr::Stack(vec![err1, err2]),
                    });
                }
                None => {
                    current_imports.insert(import.name().to_string(), import.loc().clone());
                }
            }

            // construct the path to the imported file
            let filename = format!("{}.vrs", import.name());
            importpath.push(filename);

            // cyclic import check, if we import the same thing twice, report error
            let filename = importpath.as_path().display().to_string();
            if path.contains(&filename) {
                // we have a circular dependency, find the start of the cycle
                let it = path.iter().skip_while(|e| *e != &filename);

                // convert the cycle to a string
                let s = it
                    .map(|s| s.to_string())
                    .collect::<Vec<String>>()
                    .join(" -> ");

                let msg = format!("circular dependency detected:\n  {s} -> {filename}");
                let hint = "try removing the following import";
                let e = VelosiParserErrBuilder::new(msg)
                    .add_tokstream(import.loc().clone())
                    .add_hint(hint.to_string())
                    .build();
                return Err(VelosiParserError::ImportFailure { e });
            }

            // no duplicate import, no cycile, we can parse the file now, and recurse
            let result = match Self::parse_file(filename.as_str(), false) {
                Ok(pt) => Self::do_resolve_imports(pt, path),
                Err(e) => Err(e),
            };

            match result {
                Ok(pt) => {
                    resolved_imports.push(pt);
                }
                Err(VelosiParserError::ReadSourceFile { e: _ }) => {
                    let msg = format!("Failed to resolve error: file not found: {filename}");
                    let hint = "Remove this import or ensure the module is part of the search path";
                    let e = VelosiParserErrBuilder::new(msg)
                        .add_tokstream(import.loc().clone())
                        .add_hint(hint.to_string())
                        .build();
                    return Err(VelosiParserError::ImportFailure { e });
                }
                Err(VelosiParserError::ImportFailure { e }) => {
                    let msg = format!("failed to resolve {filename}");
                    let hint = "Imported from here.";
                    let err = VelosiParserErrBuilder::new(msg)
                        .add_tokstream(import.loc().clone())
                        .add_hint(hint.to_string())
                        .build();

                    let e = VelosiParserErr::Stack(vec![e, err]);
                    return Err(VelosiParserError::ImportFailure { e });
                }
                Err(VelosiParserError::ParsingFailure { e }) => {
                    let msg = format!("failed to resolve {filename}");
                    let hint = "Imported from here.";
                    let err = VelosiParserErrBuilder::new(msg)
                        .add_tokstream(import.loc().clone())
                        .add_hint(hint.to_string())
                        .build();

                    let e = VelosiParserErr::Stack(vec![e, err]);
                    return Err(VelosiParserError::ImportFailure { e });
                }
                Err(e) => {
                    panic!("unhandled error: {:?}", e)
                }
            }

            // restore the current import path
            importpath.pop();
        }

        // remove ourselves from the sequence of import
        path.pop();

        Ok(ImportResolver::new(ptree, resolved_imports))
    }

    /// Resolves the imports of the given [VelosiParseTree]
    pub fn resolve_imports(ptree: VelosiParseTree) -> Result<VelosiParseTree, VelosiParserError> {
        // get the path context for circle detection
        let mut importpath = Vec::new();
        let import_resolver = Self::do_resolve_imports(ptree, &mut importpath)?;

        Ok(import_resolver.flatten())
    }
}

struct ImportResolver {
    parsetree: VelosiParseTree,
    imports: Vec<ImportResolver>,
}

impl ImportResolver {
    pub fn new(parsetree: VelosiParseTree, imports: Vec<ImportResolver>) -> Self {
        Self { parsetree, imports }
    }

    fn do_flatten(mut self, imported: &mut HashSet<String>) -> VelosiParseTree {
        let c = if let Some(s) = &self.parsetree.context {
            s.clone()
        } else {
            "$buf".to_string()
        };

        // already imported, just return an empty parse tree
        if imported.contains(&c) {
            return VelosiParseTree::empty();
        }

        // go through the imports and recurse
        let mut ps = VelosiParseTree::new(Vec::new());
        for import in self.imports.drain(..) {
            // recurse and merge
            let pt = import.do_flatten(imported);
            ps.merge(pt);
        }

        // remove the imports from the current parsetree
        self.parsetree.filter_imports();
        ps.merge(self.parsetree);
        imported.insert(c.clone());

        ps.set_context(c);
        ps
    }

    pub fn flatten(self) -> VelosiParseTree {
        let mut imported = HashSet::new();
        self.do_flatten(&mut imported)
    }
}

// #[cfg(test)]
// use std::path::PathBuf;

// /// test parsing of files
// #[test]
// fn parsing_imports() {
//     let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
//     d.push("tests/imports");

//     for f in vec!["basicimport.vrs", "multiimport.vrs"] {
//         d.push(f);
//         let filename = format!("{}", d.display());

//         println!("filename: {}", filename);

//         // lex the file
//         let err = Parser::parse_file(&filename);
//         assert!(err.is_ok());

//         d.pop();
//     }
// }

// /// test parsing of files
// #[test]
// fn parsing_consts() {
//     let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
//     d.push("tests/parser");

//     for f in vec!["consts.vrs", "consts2.vrs"] {
//         d.push(f);
//         let filename = format!("{}", d.display());

//         println!("filename: {}", filename);

//         // lex the file
//         let err = Parser::parse_file(&filename);
//         assert!(err.is_ok());

//         d.pop();
//     }
// }
