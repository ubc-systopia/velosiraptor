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

//! Velosiraptor Lexer Tokens
//!

use std::fmt;

use super::sourcepos::SourcePos;

/// Represents a token.
#[derive(PartialEq, Debug, Clone)]
pub enum Token<'a> {
    Identifier { id: String, pos: SourcePos<'a> },
}

impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tokstr = match self {
            Token::Identifier { id, pos } => format!("Identifier({})", id),
        };
        write!(f, "{}", tokstr)
    }
}

/// A sequence of recognized tokens that is produced by the lexer
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct TokenStream<'a> {
    /// a slice of tokens
    tokens: &'a [Token<'a>],

    /// Holds the start position of the slice relative to the full slice
    start: usize,

    /// Holds the end position of the slice relative to the full slice
    end: usize,
}

impl<'a> TokenStream<'a> {
    pub fn from_slice(tokens: &'a [Token<'a>]) -> Self {
        TokenStream {
            tokens,
            start: 0,
            end: tokens.len(),
        }
    }

    pub fn empty() -> Self {
        TokenStream {
            tokens: &[],
            start: 0,
            end: 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    pub fn as_slice(&self) -> &'a [Token<'a>] {
        self.tokens
    }
}

/// support for printing the token
impl<'a> fmt::Display for TokenStream<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut tok = String::new();
        for i in &self.tokens[0..5] {
            tok.push_str(&format!("    - {}\n", i))
        }
        if self.tokens.len() > 5 {
            tok.push_str("...\n")
        }
        if self.tokens.len() <= 5 {
            tok.push_str("<eof>\n")
        }

        write!(f, "Tokens[{}..{}:\n{}", self.start, self.end, tok)
    }
}
