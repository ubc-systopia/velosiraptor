// Velosilexer -- a lexer for the Velosiraptor Language
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

//! # VelosiLexer -- The Velosiraptor Lexer
//!
//! The VelosiLexer consumes the input file and produces a stream of tokens for
//! the parser to consume.

// used standard library functionality

use std::fs;
use std::io::Error;

// external dependencies
use custom_error::custom_error;
use nom;

pub use tokstream::{SrcSpan, Token, TokenKind, TokenStream};

// use crate::error::{IResult, VrsError};

// crate modules
mod error;
mod lexer;
mod tokens;

pub use error::VelosiLexerError as Reason;
pub use tokens::{VelosiKeyword, VelosiOpToken, VelosiTokenKind};

// /// define the lexer error type
// pub type LexErr = VrsError<SourcePos>;

/// the type for the VelosiLexer tokens
pub type VelosiToken = Token<VelosiTokenKind>;
pub type VelosiTokenStream = TokenStream<VelosiTokenKind>;

// // custom error definitions
custom_error! {pub VelosiLexerError
    ReadSourceFile {e: Error} = "Could not read the source file.",
    LexingFailure {r: Reason}   = "Lexing failed.",
    LexingIncomplete = "Needed more input to complete lexing."

}

/// represents the lexer state
pub struct VelosiLexer;

impl VelosiLexer {
    /// Lexes the supplied [SrcSpan] and converts it into a [TokenStream]
    ///
    /// This function will create a new `SrcSpan` from the supplied string.
    pub fn lex_srcspan(content: SrcSpan) -> Result<VelosiTokenStream, VelosiLexerError> {
        match lexer::lex(content) {
            Ok((_, tokens)) => Ok(TokenStream::new(tokens)),
            Err(nom::Err::Error(r)) => Err(VelosiLexerError::LexingFailure { r }),
            Err(nom::Err::Failure(r)) => Err(VelosiLexerError::LexingFailure { r }),
            _ => Err(VelosiLexerError::LexingIncomplete),
        }
    }

    /// Lexes the supplied string and converts it into a [TokenStream]
    ///
    /// This function will create a new `SrcSpan` from the supplied string.
    pub fn lex_string(content: String) -> Result<VelosiTokenStream, VelosiLexerError> {
        let sp = SrcSpan::new(content);
        VelosiLexer::lex_srcspan(sp)
    }

    /// Lexes the supplied file and converts it into a [TokenStream]
    pub fn lex_file(filename: &str) -> Result<VelosiTokenStream, VelosiLexerError> {
        let file_contents = fs::read_to_string(filename);
        match file_contents {
            Ok(content) => {
                let sp = SrcSpan::with_context(content, filename.to_string());
                VelosiLexer::lex_srcspan(sp)
            }
            Err(e) => Err(VelosiLexerError::ReadSourceFile { e }),
        }
    }
}

// impl VelosiLexer {
//     /// Constructs a vector of Tokens corresponding to Lexemes for the SourcePos
//     ///
//     /// During the lexing process, all whitespace wil be dropped. Comments remain
//     /// as Tokens.
//     pub fn lex_source_pos(sp: SourcePos) -> Result<Vec<Token>, LexerError> {
//         log::debug!("start lexing...");

//         // match the tokens
//         let (i, mut tok) = match many0(tokens)(sp) {
//             Ok((r, tok)) => (r, tok),
//             Err(Err::Failure(error)) => return Err(LexerError::LexerFailure { error }),
//             e => panic!("should not hit this branch: {:?}", e),
//         };

//         log::debug!("lexing done.");
//         // adding the end of file token
//         tok.push(Token::new(VelosiTokenKind::Eof, i));
//         Ok(tok)
//     }

//     /// Performs lexing on a file given by the filename.
//     ///
//     /// Opens and reads the file contents, and lexes it. Besides a vector of tokens,
//     /// it also returns a reference-counded String of the file contents.
//     pub fn lex_file(filename: &str) -> Result<(Vec<Token>, Rc<String>), LexerError> {
//         log::info!("creating file parser for '{}'", filename);

//         // read the file
//         let file_contents = fs::read_to_string(&filename);

//         // create a new reference counted String object
//         let contents = match file_contents {
//             Ok(s) => Rc::new(s),
//             _ => {
//                 log::error!("could not read the file '{}'", filename);
//                 return Err(LexerError::ReadSourceFile {
//                     file: filename.to_string(),
//                 });
//             }
//         };

//         // Create the new source position
//         let sp = SourcePos::from_string(Rc::new(filename.to_string()), contents.clone());

//         // lex it and return the result along with the file contents
//         match Lexer::lex_source_pos(sp) {
//             Ok(toks) => Ok((toks, contents)),
//             Err(x) => Err(x),
//         }
//     }
// }

// #[cfg(test)]
// use std::path::PathBuf;

// #[cfg(test)]
// use nom::Slice;

// /// Operator lexing tests
// #[test]
// fn operator_tests() {
//     let contents = "+++";
//     let sp = SourcePos::new("stdio", contents);
//     assert_eq!(
//         Lexer::lex_string("stdio", contents),
//         Lexer::lex_source_pos(sp.clone())
//     );
//     assert_eq!(
//         Lexer::lex_source_pos(sp.clone()),
//         Ok(vec![
//             Token::new(VelosiTokenKind::Plus, sp.slice(0..1)),
//             Token::new(VelosiTokenKind::Plus, sp.slice(1..2)),
//             Token::new(VelosiTokenKind::Plus, sp.slice(2..3)),
//             Token::new(VelosiTokenKind::Eof, sp.slice(3..3))
//         ])
//     );

//     let contents = "==+<<>";
//     let sp = SourcePos::new("stdio", contents);
//     assert_eq!(
//         Lexer::lex_source_pos(sp.clone()),
//         Ok(vec![
//             Token::new(VelosiTokenKind::Eq, sp.slice(0..2)),
//             Token::new(VelosiTokenKind::Plus, sp.slice(2..3)),
//             Token::new(VelosiTokenKind::LShift, sp.slice(3..5)),
//             Token::new(VelosiTokenKind::Gt, sp.slice(5..6)),
//             Token::new(VelosiTokenKind::Eof, sp.slice(6..6))
//         ])
//     );
// }

// /// test lexing of files
// #[test]
// fn basics() {
//     let content = "import foobar; /* comment */unit abc {}; // end of file";
//     let tok = match Lexer::lex_string("stdio", content) {
//         Ok(vec) => vec,
//         Err(_) => panic!("lexing failed"),
//     };
//     // there should be 10 tokens
//     assert_eq!(tok.len(), 11);
// }

// /// test lexing of files
// #[test]
// fn empty_file_tests() {
//     let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
//     d.push("tests/lexer");

//     for f in vec!["emptyfile.vrs", "whitespace.vrs"] {
//         d.push(f);
//         let filename = format!("{}", d.display());

//         // lex the file
//         let err = Lexer::lex_file(&filename);
//         assert!(err.is_ok());

//         d.pop();
//     }

//     for f in vec!["comments.vrs"] {
//         d.push(f);
//         let filename = format!("{}", d.display());

//         // lex the file
//         let err = Lexer::lex_file(&filename);
//         assert!(err.is_ok());

//         d.pop();
//     }
// }

// /// test lexing of files
// #[test]
// fn files_tests() {
//     let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
//     d.push("tests/lexer");

//     for f in vec!["sample.vrs"] {
//         d.push(f);
//         let filename = format!("{}", d.display());

//         // lex the file
//         let err = Lexer::lex_file(&filename);
//         assert!(err.is_ok());
//         d.pop();
//     }
// }

// /// test lexing of files
// #[test]
// fn basic_failure_tests() {
//     let contents = "foo /* bar";
//     assert!(Lexer::lex_source_pos(SourcePos::new("stdio", contents)).is_err());
//     let contents = "12344asdf";
//     assert!(Lexer::lex_source_pos(SourcePos::new("stdio", contents)).is_err());
//     let contents = "foo11`basr";
//     assert!(Lexer::lex_source_pos(SourcePos::new("stdio", contents)).is_err());
// }

// /// test lexing of files
// #[test]
// fn files_with_failures_tests() {
//     let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
//     d.push("tests/lexer");

//     for f in vec!["commentsfail.vrs", "tokenfail.vrs"] {
//         d.push(f);
//         let filename = format!("{}", d.display());

//         // lex the file
//         let err = Lexer::lex_file(&filename);
//         assert!(err.is_err());
//         d.pop();
//     }
// }
