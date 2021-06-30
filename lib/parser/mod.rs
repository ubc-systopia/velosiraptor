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

pub mod ast;
pub mod terminals;
use ast::Ast;

mod imports;

use super::lexer::token::{Token, TokenStream};
use super::lexer::Lexer;

// custom error definitions
custom_error! {#[derive(PartialEq)] pub ParserError
  LexerFailure               = "The lexer failed on the file.",
  ParserFailure              = "The parser has failed",
  NotYetImplemented          = "Not Yet Implemented"
}

pub struct Parser;

impl Parser {
    pub fn parse_string<'a>(context: &str, string: &'a str) -> Result<Ast, ParserError> {
        log::info!("creating string parser");
        let tokens = match Lexer::lex_string(context, string) {
            Ok(toks) => toks,
            Err(_x) => return Err(ParserError::LexerFailure),
        };
        Parser::parse_tokens(&tokens)
    }

    // pub fn parse_file<'a>(filename: &'a str) -> Result<(Ast,  &'a str), ParserError> {
    //     log::info!("creating file parser for '{}'", filename);
    //     let (tokens, content) = match Lexer::lex_file(filename) {
    //         Ok((tokens, content)) => (tokens, content),
    //         Err(_x) => return Err(ParserError::LexerFailure)
    //     };

    //     match Parser::parse_tokens(&tokens) {
    //         Ok(ast) => Ok((ast, &content)),
    //         Err(x)  => Err(x)
    //     }
    // }

    pub fn parse_tokens<'a>(tokens: &[Token<'a>]) -> Result<Ast, ParserError> {
        let _tokstream = TokenStream::from_slice(&tokens);
        Err(ParserError::NotYetImplemented)
    }
}
