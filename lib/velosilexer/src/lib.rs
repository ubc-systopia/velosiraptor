// Velosilexer -- a lexer for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2021-2023 Systopia Lab, Computer Science, University of British Columbia
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
use tokstream::{SrcSpan, Tok, TokStream};

// crate modules
mod error;
mod lexer;
mod tokens;

// re-exports
pub use error::VelosiLexerErr;
pub use tokens::{VelosiKeyword, VelosiOpToken, VelosiTokenKind};

/// the type for the VelosiLexer tokens
pub type VelosiToken = Tok<VelosiTokenKind>;
pub type VelosiTokenStream = TokStream<VelosiTokenKind>;

// custom error definitions
custom_error! {pub VelosiLexerError
    ReadSourceFile {e: Error} = "Could not read the source file.",
    LexingFailure {r: VelosiLexerErr}   = "Lexing failed.",
    LexingIncomplete = "Needed more input to complete lexing."
}

/// represents the lexer state
pub struct VelosiLexer;

impl VelosiLexer {
    /// Lexes the supplied string and converts it into a [VelosiTokenStream]
    ///
    /// White space characters are removed and are not present in the returned token stream.
    /// Comments will be part of the tokens.
    ///
    /// This function will create a new `SrcSpan` from the supplied string.
    ///
    /// # Arguments
    ///
    /// * `content` - the string to be lexed
    ///
    /// # Returns
    ///
    /// Returns a [VelosiTokenStream] if the file was successfully read and lexxed into tokens.
    /// Otherwise, it returns an [VelosiTokenKind].
    ///
    pub fn lex_string(content: String) -> Result<VelosiTokenStream, VelosiLexerError> {
        let sp = SrcSpan::new(content);
        VelosiLexer::lex_srcspan(sp)
    }

    /// Lexes the supplied file and converts it into a [VelosiTokenStream]
    ///
    /// White space characters are removed and are not present in the returned token stream.
    /// Comments will be part of the tokens.
    ///
    /// # Arguments
    ///
    /// * `filename` - the name of the file to be lexed
    ///
    /// # Returns
    ///
    /// Returns a [VelosiTokenStream] if the file was successfully read and lexxed into tokens.
    /// Otherwise, it returns an [VelosiLexerError].
    ///
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

    /// Lexes the supplied [SrcSpan] and converts it into a [VelosiTokenStream]
    ///
    /// # Arguments
    ///
    /// * `content` - source span to be lexed
    ///
    /// # Returns
    ///
    /// Returns a [VelosiTokenStream] if the file was successfully read and lexxed into tokens.
    /// Otherwise, it returns an [VelosiLexerError].
    ///
    fn lex_srcspan(content: SrcSpan) -> Result<VelosiTokenStream, VelosiLexerError> {
        match lexer::lex(content) {
            Ok((_, tokens)) => Ok(TokStream::new_filtered(tokens)),
            Err(nom::Err::Error(r)) => Err(VelosiLexerError::LexingFailure { r }),
            Err(nom::Err::Failure(r)) => Err(VelosiLexerError::LexingFailure { r }),
            _ => Err(VelosiLexerError::LexingIncomplete),
        }
    }
}
