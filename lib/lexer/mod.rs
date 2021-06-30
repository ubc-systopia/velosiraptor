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
#[cfg(test)]
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
pub struct Lexer;

impl Lexer {
    pub fn lex_string<'a>(context: &'a str, string: &'a str) -> Result<Vec<Token<'a>>, LexerError> {
        let sp = SourcePos::new(context, string);
        Ok(Vec::new())
    }

    // pub fn lex_file<'a>(filename: &'a str) -> Result<(Vec<Token<'a>>, &'a str), LexerError> {
    //     log::info!("creating file parser for '{}'", filename);
    //     let file_contents = fs::read_to_string(&filename);
    //     let contents = match file_contents {
    //         Ok(s) => s,
    //         _ => {
    //             log::error!("could not read the file '{}'", filename);
    //             return Err(LexerError::ReadSourceFile { file: filename.to_string() });
    //         }
    //     };
    //     match Lexer::lex_string(filename, &contents) {
    //         Ok(toks) => Ok((toks, contents)),
    //         Err(x) => Err(x),
    //     }
    // }
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
        let err = Lexer::lex_file(&filename);
        assert!(err.is_ok());

        // lex the file

        d.pop();
    }
}
