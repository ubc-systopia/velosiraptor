// Velosiraptor Parser
//
//
// MIT License
//
// Copyright (c) 2021 Systopia Lab, Computer Science, University of British Columbia
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

//! Parser Module of the Velosiraptor Compiler

use custom_error::custom_error;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

pub mod terminals;
//mod state;
mod bitslice;
mod expression;
mod field;
mod import;
mod statement;

mod constdef;
mod unit;

use crate::ast::Ast;
use constdef::constdef;
use import::import;
use terminals::eof;
use unit::unit;

use super::lexer::{LexErr, Lexer, LexerError};
use super::token::{Token, TokenStream};
use crate::error::VrsError;

/// define the lexer error type
pub type ParsErr = VrsError<TokenStream>;

// custom error definitions
custom_error! {#[derive(PartialEq)] pub ParserError
    IOError { file: String }       = "The input file could not be read.",
    LexerFailure {error: LexErr }  = "The lexer failed on the file.",
    ParserFailure                  = "The parser has failed",
    ParserIncomplete               = "The parser didn't finish",
    NotYetImplemented              = "Not Yet Implemented"
}

/// Implementation of [std::convert::From<LexerError>] for [VrsError]
///
/// This converts from a lexer error to a parser error
impl From<LexerError> for ParserError {
    fn from(e: LexerError) -> Self {
        use LexerError::*;
        match e {
            ReadSourceFile { file } => ParserError::IOError { file },
            LexerFailure { error } => ParserError::LexerFailure { error },
        }
    }
}

pub struct Parser;

use nom::multi::many0;

impl Parser {
    /// Parses a token vector and creates an [Ast]
    pub fn parse(context: &str, tokens: Vec<Token>) -> Result<Ast, ParserError> {
        log::debug!("start parsing...");

        // get the token stream
        let tokstream = TokenStream::from_vec(tokens);

        // a parsing unit consists of zero or more imports
        let (i1, importlist) = match many0(import)(tokstream) {
            Ok((r, i)) => (r, i),
            Err(_) => return Err(ParserError::ParserFailure),
        };
        let mut imports = HashMap::new();
        for i in importlist {
            imports.insert(i.name.clone(), i);
        }

        // a parsing unit consists of zero or more imports
        let (i2, constlist) = match many0(constdef)(i1) {
            Ok((r, i)) => (r, i),
            Err(_) => return Err(ParserError::ParserFailure),
        };

        let mut consts = HashMap::new();
        for i in constlist {
            consts.insert(i.ident().to_string(), i);
        }

        // there must be at least one unit definition
        let i3 = i2;
        // let (rem, unitlist) = match many0(unit)(i2) {
        //     Ok((rem, p)) => (rem, p),
        //     Err(_) => return Err(ParserError::ParserFailure),
        // };

        let mut units = HashMap::new();
        // for i in unitlist {
        //     units.insert(i.name.clone(), i);
        // }

        // consume the end of file token
        log::debug!("parsing done.");
        match eof(i3) {
            Ok(_) => Ok(Ast {
                filename: context.to_string(),
                imports,
                consts,
                units,
            }),
            Err(_) => Err(ParserError::ParserIncomplete),
        }
    }

    /// Parses a supplied string by lexing it first, create an Ast
    pub fn parse_string(context: &str, string: &str) -> Result<Ast, ParserError> {
        log::info!("creating string parser");
        let tokens = Lexer::lex_string(context, string)?;
        Parser::parse_tokens(context, &tokens)
    }

    /// Parses a file by lexing it first, create an Ast
    pub fn parse_file(filename: &str) -> Result<(Ast, Rc<String>), ParserError> {
        log::info!("creating file parser for '{}'", filename);
        let (tokens, content) = Lexer::lex_file(filename)?;

        let ast = Parser::parse_tokens(filename, &tokens)?;
        Ok((ast, content))
    }

    /// Parses a slice of tokens
    ///
    /// This will create a new vector of the token slice
    pub fn parse_tokens(context: &str, tokens: &[Token]) -> Result<Ast, ParserError> {
        Parser::parse(context, tokens.to_vec())
    }
}

#[cfg(test)]
use std::path::PathBuf;

/// test parsing of files
#[test]
fn parsing_imports() {
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("tests/imports");

    for f in vec!["basicimport.vrs", "multiimport.vrs"] {
        d.push(f);
        let filename = format!("{}", d.display());

        println!("filename: {}", filename);

        // lex the file
        let err = Parser::parse_file(&filename);
        assert!(err.is_ok());

        d.pop();
    }
}

/// test parsing of files
#[test]
fn parsing_consts() {
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("tests/parser");

    for f in vec!["consts.vrs", "consts2.vrs"] {
        d.push(f);
        let filename = format!("{}", d.display());

        println!("filename: {}", filename);

        // lex the file
        let err = Parser::parse_file(&filename);
        assert!(err.is_ok());

        d.pop();
    }
}
