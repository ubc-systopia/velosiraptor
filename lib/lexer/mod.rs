// Velosiraptor Lexer
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

//! Lexer Module of the Velosiraptor Compiler

use custom_error::custom_error;
use std::fs;
use std::path::PathBuf;

pub mod token;
use self::token::*;

pub mod sourcepos;
use self::sourcepos::SourcePos;

// custom error definitions
custom_error! {#[derive(PartialEq)] pub LexerError
  ReadSourceFile{ file: String } = "Could not read the source file",
  NoTokens                       = "No tokens found. Need to lex first"
}

/// represents the lexer state
pub struct Lexer<'a> {
    /// the filename that is being parser
    filename: String,

    /// the contents of this file
    filecontents: String,

    ///
    tokens: Vec<Token<'a>>,
}

impl<'a> Lexer<'a> {
    ///
    pub fn new(filename: String, filecontents: String) -> Result<Lexer<'a>, LexerError> {
        Ok(Lexer {
            filename,
            filecontents,
            tokens: Vec::new(),
        })
    }

    pub fn from_string(contents: String) -> Result<Lexer<'a>, LexerError> {
        log::info!("creating string parser");
        Lexer::new("<stdio>".to_string(), contents)
    }

    pub fn from_file(filename: String) -> Result<Lexer<'a>, LexerError> {
        log::info!("creating file parser for '{}'", filename);
        let file_contents = fs::read_to_string(&filename);
        let contents = match file_contents {
            Ok(s) => s,
            _ => {
                log::error!("could not read the file '{}'", filename);
                return Err(LexerError::ReadSourceFile { file: filename });
            }
        };
        Lexer::new(filename, contents)
    }

    /// performs the lexing of the tokens
    pub fn lex_tokens(&mut self) -> Result<(), LexerError> {
        log::info!("parsing: {}", self.filename);
        log::debug!("<contents>");
        log::debug!("{}", &self.filecontents);
        log::debug!("<contents>");

        // create the source position struct
        let sp = SourcePos::new(&self.filename, &self.filecontents);

        // call lexer here...

        Ok(())
    }

    pub fn filter_comments(&mut self) {
        let mut i = 0;
        while i < self.tokens.len() {
            match self.tokens[i] {
                //Comment(_) => {self.tokens.remove(i);},
                _ => {
                    i = i + 1;
                }
            };
        }
    }

    pub fn get_tokens(&self) -> Result<&[Token<'a>], LexerError> {
        if self.tokens.is_empty() {
            Err(LexerError::NoTokens)
        } else {
            Ok(self.tokens.as_slice())
        }
    }

    pub fn get_token_stream(&self) -> Result<TokenStream, LexerError> {
        match self.get_tokens() {
            Ok(t) => Ok(TokenStream::from_slice(t)),
            Err(x) => Err(x),
        }
    }
}

#[test]
/// tests lexing of files
fn import_tests() {
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("tests/lexer");

    for f in vec!["emptyfile.vrs", "comments.vrs", "whitespace.vrs"] {
        d.push(f);
        let filename = format!("{}", d.display());

        // create the lexer
        let mut lexer = Lexer::from_file(filename).expect("failed to construct the parser");

        // lex the file
        let err = lexer.lex_tokens();
        assert!(err.is_ok());

        d.pop();
    }
}
