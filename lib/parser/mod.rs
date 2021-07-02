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

use custom_error::custom_error;
use std::rc::Rc;

pub mod ast;
pub mod terminals;
use ast::Ast;

mod import;
use import::import;

mod unit;
use unit::unit;

//mod state;
mod bitslice;
mod field;

use super::lexer::token::{Token, TokenStream};
use super::lexer::Lexer;

// custom error definitions
custom_error! {#[derive(PartialEq)] pub ParserError
  LexerFailure               = "The lexer failed on the file.",
  ParserFailure              = "The parser has failed",
  NotYetImplemented          = "Not Yet Implemented"
}

pub struct Parser;

use nom::multi::{many0, many1};

impl Parser {
    /// Parses a token vector and creates an [Ast]
    pub fn parse(tokens: Vec<Token>) -> Result<Ast, ParserError> {
        log::debug!("start parsing...");

        // get the token stream
        let tokstream = TokenStream::new(tokens);

        // a parsing unit consists of zero or more imports
        let (i1, _imports) = match many0(import)(tokstream) {
            Ok((r, i)) => (r, i),
            Err(_) => return Err(ParserError::ParserFailure),
        };

        // there must be at least one unit definition
        let (rem, _units) = match many1(unit)(i1) {
            Ok((rem, p)) => (rem, p),
            Err(_) => return Err(ParserError::ParserFailure),
        };

        // the input must be fully consumed
        if !rem.is_empty() {
            return Err(ParserError::ParserFailure);
        }

        log::debug!("parsing done.");
        Err(ParserError::NotYetImplemented)
    }

    /// Parses a supplied string by lexing it first, create an Ast
    pub fn parse_string(context: &str, string: &str) -> Result<Ast, ParserError> {
        log::info!("creating string parser");
        let tokens = match Lexer::lex_string(context, string) {
            Ok(toks) => toks,
            Err(_x) => return Err(ParserError::LexerFailure),
        };
        Parser::parse_tokens(&tokens)
    }

    /// Parses a file by lexing it first, create an Ast
    pub fn parse_file(filename: &str) -> Result<(Ast,  Rc<String>), ParserError> {
        log::info!("creating file parser for '{}'", filename);
        let (tokens, content) = match Lexer::lex_file(filename) {
            Ok((tokens, content)) => (tokens, content),
            Err(_x) => return Err(ParserError::LexerFailure)
        };

        match Parser::parse_tokens(&tokens) {
            Ok(ast) => Ok((ast, content)),
            Err(x)  => Err(x)
        }
    }

    /// Parses a slice of tokens
    ///
    /// This will create a new vector of the token slice
    pub fn parse_tokens(tokens: &[Token]) -> Result<Ast, ParserError> {
        Parser::parse(tokens.to_vec())
    }
}
