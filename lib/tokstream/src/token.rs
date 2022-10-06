// Token
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

//! Token Representation

// used standard library modules
use std::fmt::{Display, Formatter, Result};

// used third-party libraries
use srcspan::{SrcLoc, SrcSpan};

/// Trait to be implemented by the TokenKind types
pub trait TokenKind {
    /// whether the token is a keyword
    fn is_keyword(&self) -> bool;

    /// whether the token has a reserved value
    fn is_reserved(&self) -> bool;

    /// whether the token is a comment
    fn is_comment(&self) -> bool;

    /// whether the token is a literal, string or number, keyword, ...
    fn is_literal(&self) -> bool;

    /// whether the token is an identifier
    fn is_identifier(&self) -> bool;

    /// whether the token represents a type
    fn is_type(&self) -> bool;
}

/// Represents a Lexical Token
///
/// The Token is parameterised
#[derive(PartialEq, Eq, Clone)]
pub struct Token<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// the kind of the token, defining its type
    kind: T,

    /// the source position of the toke
    span: SrcSpan,
}

/// The Token Implementation
impl<T> Token<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// Creates a new [Token] with the given kind and source span
    pub fn new(kind: T, span: SrcSpan) -> Self {
        Token { kind, span }
    }

    /// Obtains the source span for this token
    pub fn span(&self) -> &SrcSpan {
        &self.span
    }

    /// Obtains the kind of this token
    pub fn kind(&self) -> &T {
        &self.kind
    }

    /// Returns the start of the location of this token
    pub fn loc(&self) -> &SrcLoc {
        self.span.loc()
    }

    /// returns true if the token is a keyword
    pub fn is_keyword(&self) -> bool {
        self.kind.is_keyword()
    }

    /// returns true if the token is a reserved identifier
    pub fn is_reserved(&self) -> bool {
        self.kind.is_reserved()
    }
}

/// Implementation of the [std::Display] trait for [Token]
impl<T> Display for Token<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    fn fmt(&self, f: &mut Formatter) -> Result {
        Display::fmt(&self.kind, f)
    }
}
