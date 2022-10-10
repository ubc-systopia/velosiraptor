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

use std::io::Error;

// external dependencies
use custom_error::custom_error;

pub use velosilexer::{
    VelosiKeyword, VelosiLexer, VelosiLexerError, VelosiOpToken, VelosiTokenKind, VelosiTokenStream,
};

// crate modules
mod error;
mod parser;
mod parsetree;

use error::VelosiParserErr;
pub use parsetree::{VelosiParseTree, VelosiParseTreeContextNode, VelosiParseTreeTypeInfo};

// // custom error definitions
custom_error! {pub VelosiParserError
    ReadSourceFile {e: Error} = "Could not read the source file.",
    LexingFailure { e: VelosiLexerError }   = "Lexing failed.",
    ParsingFailure { e: VelosiParserErr } = "Parsing failed.",
}

/// represents the lexer state
pub struct VelosiParser;

impl VelosiParser {
    /// Parses the supplied [TokenStream] and converts it into a [VelosiParseTree]
    ///
    /// This function will create a new `VelosiParseTree` from the supplied string.
    pub fn parse_tokstream(
        content: VelosiTokenStream,
    ) -> Result<VelosiParseTree, VelosiParserError> {
        let ts = content.with_retained(|t| t.keep());
        match parser::parse(ts) {
            Ok((_, tree)) => Ok(tree),
            Err(nom::Err::Error(e)) => Err(VelosiParserError::ParsingFailure { e }),
            Err(nom::Err::Failure(e)) => Err(VelosiParserError::ParsingFailure { e }),
            _ => Err(VelosiParserError::LexingFailure {
                e: VelosiLexerError::LexingIncomplete,
            }),
        }
    }

    /// Parses the supplied string and converts it into a [VelosiParseTree]
    ///
    /// This function will create a new `VelosiParseTree` from the supplied string.
    pub fn parse_string(content: String) -> Result<VelosiParseTree, VelosiParserError> {
        match VelosiLexer::lex_string(content) {
            Ok(tokens) => VelosiParser::parse_tokstream(tokens),
            Err(e) => Err(VelosiParserError::LexingFailure { e }),
        }
    }

    /// Parses the supplied file and converts it into a [VelosiParseTree]
    pub fn parse_file(filename: &str) -> Result<VelosiParseTree, VelosiParserError> {
        match VelosiLexer::lex_file(filename) {
            Ok(tokens) => VelosiParser::parse_tokstream(tokens),
            Err(VelosiLexerError::ReadSourceFile { e }) => {
                Err(VelosiParserError::ReadSourceFile { e })
            }
            Err(e) => Err(VelosiParserError::LexingFailure { e }),
        }
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
