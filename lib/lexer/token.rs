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

use nom::{InputIter, InputLength, InputTake, Needed, Slice};
use std::fmt;
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};

use super::sourcepos::SourcePos;

/// Represents the content of a token
#[derive(PartialEq, Debug, Clone)]
pub enum TokenContent {
    EOF,
    Illegal,
    // identifiers and literals
    Identifier(String),
    StringLiteral(String),
    IntLiteral(i64),
    BoolLiteral(bool),
    // comments
    Comment(String),
    BlockComment(String),
    // statements
    Unit,
    State,
    Memory,
    Registers,
    // punctuations
    Comma,
    Colon,
    SemiColon,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    // operators
    Plus,
    Minus,
    Multiply,
    LShift,
    RShift,
    Equal,
}

/// Represents a token.
#[derive(PartialEq, Debug, Clone)]
pub struct Token<'a> {
    pub content: TokenContent,
    pub spos: SourcePos<'a>,
}

impl<'a> Token<'a> {
    fn new(content: TokenContent, spos: SourcePos<'a>) -> Self {
        Token { content, spos }
    }
}

impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tokstr = match &self.content {
            TokenContent::EOF => "End of File".to_string(),
            TokenContent::Illegal => "Illegal Token".to_string(),
            TokenContent::Identifier(id) => format!("Identifier({})", id),
            TokenContent::StringLiteral(st) => format!("StringLiteral({})", st),
            TokenContent::IntLiteral(n) => format!("IntLiteral({})", n),
            TokenContent::BoolLiteral(bl) => format!("BoolLiteral({})", bl),
            TokenContent::Comment(st) => format!("Comment({})", st),
            TokenContent::BlockComment(st) => format!("BlockComment({})", st),
            TokenContent::Unit => "Unit".to_string(),
            TokenContent::State => "State".to_string(),
            TokenContent::Memory => "Memory".to_string(),
            TokenContent::Registers => "Registers".to_string(),
            TokenContent::Comma => "Comma".to_string(),
            TokenContent::Colon => "Colon".to_string(),
            TokenContent::SemiColon => "SemiColon".to_string(),
            TokenContent::LParen => "LParen".to_string(),
            TokenContent::RParen => "RParen".to_string(),
            TokenContent::LBrace => "LBrace".to_string(),
            TokenContent::RBrace => "RBrace".to_string(),
            TokenContent::LBracket => "LBracket".to_string(),
            TokenContent::RBracket => "RBracket".to_string(),
            TokenContent::Plus => "Plus".to_string(),
            TokenContent::Minus => "Minus".to_string(),
            TokenContent::Multiply => "Multiply".to_string(),
            TokenContent::LShift => "LShift".to_string(),
            TokenContent::RShift => "RShift".to_string(),
            TokenContent::Equal => "Equal".to_string(),
        };
        write!(f, "{}", tokstr)
    }
}

/// Implementation of `nom::InputLength` for `Token`
impl<'a> InputLength for Token<'a> {
    #[inline]
    /// Calculates the input length, as indicated by its name, and the name of the trait itself
    fn input_len(&self) -> usize {
        1
    }
}

/// A sequence of recognized tokens that is produced by the lexer
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct TokenStream<'a> {
    /// a slice of tokens
    tokens: &'a [Token<'a>],

    /// Holds the start position of the slice relative to the full slice
    offset: usize,
}

impl<'a> TokenStream<'a> {
    pub fn from_slice(tokens: &'a [Token<'a>]) -> Self {
        TokenStream { tokens, offset: 0 }
    }

    pub fn empty() -> Self {
        TokenStream {
            tokens: &[],
            offset: 0,
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

        write!(
            f,
            "Tokens[{}..{}:\n{}",
            self.offset,
            self.offset + self.tokens.len(),
            tok
        )
    }
}

/// Implementation of `nom::InputLength` for `TokenStream`
impl<'a> InputLength for TokenStream<'a> {
    #[inline]
    /// Calculates the input length, as indicated by its name, and the name of the trait itself
    fn input_len(&self) -> usize {
        self.tokens.len()
    }
}

/// Implementation of `nom::InputTake` for `TokenStream`
impl<'a> InputTake for TokenStream<'a> {
    #[inline]
    /// Returns a slice of `count` bytes. panics if count > length
    fn take(&self, count: usize) -> Self {
        if count > self.tokens.len() {
            panic!("count > length: {} > {}", count, self.tokens.len());
        }
        TokenStream {
            tokens: &self.tokens[0..count],
            offset: self.offset,
        }
    }

    #[inline]
    /// Split the stream at the `count` byte offset. panics if count > length
    fn take_split(&self, count: usize) -> (Self, Self) {
        if count > self.tokens.len() {
            panic!("count > length: {} > {}", count, self.tokens.len());
        }
        // split the slice at position
        let (prefix, suffix) = self.tokens.split_at(count);

        // create the first half
        let first = TokenStream {
            tokens: prefix,
            offset: self.offset,
        };

        // create the second half half
        let second = TokenStream {
            tokens: suffix,
            offset: self.offset + prefix.len(),
        };

        // return
        (second, first)
    }
}

/// implementation of `nom::Slice<RangeFull>` for `TokenStream`
impl<'a> Slice<RangeFull> for TokenStream<'a> {
    fn slice(&self, _: RangeFull) -> Self {
        // return a clone of our selves
        self.clone()
    }
}

/// implementation of `nom::Slice<Range<usize>>` for `TokenStream`
impl<'a> Slice<Range<usize>> for TokenStream<'a> {
    #[inline]
    fn slice(&self, range: Range<usize>) -> Self {
        let start = range.start;
        let toks = &self.tokens[range];

        TokenStream {
            tokens: toks,
            offset: self.offset + start,
        }
    }
}

/// implementation of `nom::Slice<RangeTo<usize>>` for `TokenStream`
impl<'a> Slice<RangeTo<usize>> for TokenStream<'a> {
    #[inline]
    fn slice(&self, range: RangeTo<usize>) -> Self {
        // just return the range from 0..end
        self.slice(0..range.end)
    }
}

/// implementation of `nom::Slice<RangeFrom<usize>>` for `TokenStream`
impl<'a> Slice<RangeFrom<usize>> for TokenStream<'a> {
    #[inline]
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        // just return the range from start..end
        self.slice(range.start..self.tokens.len())
    }
}

use std::iter::Enumerate;

/// implementation of `nom::InputIter` for `TokenStream`
impl<'a> InputIter for TokenStream<'a> {
    /// The current input type is a sequence of that Item type.
    type Item = &'a Token<'a>;

    /// An iterator over the input type, producing the item and its position for use with Slice.
    type Iter = Enumerate<::std::slice::Iter<'a, Token<'a>>>;

    /// An iterator over the input type, producing the item
    type IterElem = ::std::slice::Iter<'a, Token<'a>>;

    #[inline]
    /// Returns an iterator over the elements and their byte offsets
    fn iter_indices(&self) -> Self::Iter {
        self.tokens.iter().enumerate()
    }

    #[inline]
    /// Returns an iterator over the elements
    fn iter_elements(&self) -> Self::IterElem {
        self.tokens.iter()
    }

    #[inline]
    /// Finds the byte position of the element
    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.tokens.iter().position(|b| predicate(b))
    }

    #[inline]
    /// Get the byte offset from the element's position in the stream
    fn slice_index(&self, count: usize) -> Result<usize, Needed> {
        if self.tokens.len() >= count {
            Ok(count)
        } else {
            Err(Needed::Unknown)
        }
    }
}
