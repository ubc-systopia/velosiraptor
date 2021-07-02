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

use nom::{InputIter, InputLength, InputTake, Needed, Slice};
use std::fmt;
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};
use std::rc::Rc;

use super::sourcepos::SourcePos;

/// Represents the content of a token
#[derive(PartialEq, Debug, Clone)]
pub enum TokenContent {
    Eof,
    Illegal,
    // identifiers and literals
    Identifier(String),
    StringLiteral(String),
    IntLiteral(u64),
    BoolLiteral(bool),
    // comments
    Comment(String),
    BlockComment(String),
    // statements
    Import,
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

/// Represents a lexed token.
#[derive(PartialEq, Debug, Clone)]
pub struct Token {
    /// the content of the token, defining its type
    pub content: TokenContent,

    /// the source position of the toke
    pub spos: SourcePos,
}

/// The Token Implementation
impl Token {
    /// Creats a new token with the given [TokenContent] at the [SourcePos].
    pub fn new(content: TokenContent, spos: SourcePos) -> Self {
        Token { content, spos }
    }

    /// Obtains the [SourcePos] of the token
    pub fn get_pos(&self) -> SourcePos {
        self.spos.clone()
    }

    pub fn get_symbol(&self) -> &str {
        match &self.content {
            TokenContent::Eof => "<EOF>",
            TokenContent::Illegal => "<ILLEGAL>",
            TokenContent::Identifier(id) => &id,
            TokenContent::StringLiteral(st) => &st,
            TokenContent::IntLiteral(_) => "NUMBER",
            TokenContent::BoolLiteral(bl) => {
                if *bl {
                    "true"
                } else {
                    "false"
                }
            }
            TokenContent::Comment(_) => "<COMMENT>",
            TokenContent::BlockComment(_) => "<COMMENT>",
            TokenContent::Unit => "UNIT",
            TokenContent::Import => "IMPORT",
            TokenContent::State => "STATE",
            TokenContent::Memory => "MEMORY",
            TokenContent::Registers => "REGISTERS",
            TokenContent::Comma => ",",
            TokenContent::Colon => ":",
            TokenContent::SemiColon => ";",
            TokenContent::LParen => "(",
            TokenContent::RParen => ")",
            TokenContent::LBrace => "{",
            TokenContent::RBrace => "}",
            TokenContent::LBracket => "[",
            TokenContent::RBracket => "]",
            TokenContent::Plus => "+",
            TokenContent::Minus => "-",
            TokenContent::Multiply => "*",
            TokenContent::LShift => "<<",
            TokenContent::RShift => ">>",
            TokenContent::Equal => "==",
        }
    }
}

/// Implementation of the [std::fmt::Display] trait for [Token]
impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tokstr = match &self.content {
            TokenContent::Eof => "End of File".to_string(),
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
            TokenContent::Import => "Import".to_string(),
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
impl InputLength for Token {
    #[inline]
    /// Calculates the input length, as indicated by its name, and the name of the trait itself
    fn input_len(&self) -> usize {
        1
    }
}

/// A sequence of recognized tokens that is produced by the lexer
#[derive(Clone, PartialEq, Debug)]
pub struct TokenStream {
    /// a reference counted vector of tokens
    tokens: Rc<Vec<Token>>,

    /// Holds the valid range within the [Token] vector
    range: Range<usize>,
}

/// Implementation of the [TokenStream]
impl TokenStream {
    /// Creates a new TokenStream from the supplied vector of tokens
    ///
    /// The TokenStream will cover the entire vector.
    pub fn new(tokens: Vec<Token>) -> Self {
        let len = tokens.len();
        TokenStream {
            tokens: Rc::new(tokens),
            range: 0..len,
        }
    }

    /// Creates a new [TokenStream] from the supplied [Token] slice.empty()
    ///
    /// This will create a new vector of Tokens from the supplied slice.
    pub fn from_slice(tokens: &[Token]) -> Self {
        Self::new(tokens.to_vec())
    }

    /// Creates a new [TokenStream] covering a subrange of [self]
    ///
    /// # Panics
    ///
    /// Panics if the supplied range is outside of the covered range by the [TokenStream]
    pub fn from_self(&self, range: Range<usize>) -> Self {
        assert!(self.input_len() >= range.end - range.start);
        assert!(self.range.start + range.end <= self.range.end);

        // the new range is the supplied range, shifted by the current range
        let range = self.range.start + range.start..self.range.start + range.end;

        TokenStream {
            tokens: self.tokens.clone(),
            range,
        }
    }

    /// Creates an empty TokenStream.
    pub fn empty() -> Self {
        TokenStream {
            tokens: Rc::new(Vec::new()),
            range: 0..0,
        }
    }

    /// Returns true if this TokenStream is empty
    pub fn is_empty(&self) -> bool {
        self.range.is_empty()
    }

    /// Returns the current slice of Tokens backed by this [TokenStream]
    pub fn as_slice(&self) -> &[Token] {
        &self.tokens[self.range.clone()]
    }

    /// Returns the first [Token] in the [TokenStream]
    pub fn peek(&self) -> &Token {
        &self.tokens[self.range.start]
    }

    /// Obtains the [SourcePos] of the current [Token] in the [TokenStream]
    pub fn input_sourcepos(&self) -> SourcePos {
        self.peek().spos.clone()
    }

    /// Obtains the current range relative to the entire [TokenStream]
    pub fn input_range(&self) -> Range<usize> {
        self.range.clone()
    }

    /// Returns a slice covering the entire input tokens.
    pub fn input_tokens(&self) -> &[Token] {
        &self.tokens
    }
}

/// Implements the [std::fmt::Display] trait for [TokenStream]
impl fmt::Display for TokenStream {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let len = std::cmp::min(self.input_len(), 5);
        let mut tok = String::new();
        for i in &self.tokens[self.range.start..self.range.start + len] {
            tok.push_str(&format!("    - {}\n", i))
        }
        if self.input_len() > 5 {
            tok.push_str("    - ...\n")
        }
        if self.input_len() <= 5 {
            tok.push_str("    - <eof>\n")
        }

        write!(f, "Tokens[{:?}]:\n{}", self.range.clone(), tok)
    }
}

/// Implementation of the [nom::InputLength] trait for [TokenStream]
impl InputLength for TokenStream {
    #[inline]
    /// Calculates the input length, as indicated by its name, and the name of the trait itself
    fn input_len(&self) -> usize {
        self.range.end - self.range.start
    }
}

/// Implementation of the [nom::InputTake] trait for [TokenStream]
impl InputTake for TokenStream {
    #[inline]
    /// Returns a new [TokenStream] covering the first `count` tokens.
    ///
    /// # Panics
    ///
    /// The function panics if count > self.input_len()
    fn take(&self, count: usize) -> Self {
        assert!(count <= self.input_len());
        self.from_self(0..count)
    }

    #[inline]
    /// Split the [TokenStream] at the `count` tokens.
    ///
    /// # Panics
    /// The function panics if count > self.input_len()
    fn take_split(&self, count: usize) -> (Self, Self) {
        assert!(count <= self.input_len());

        let first = self.from_self(0..count);
        let second = self.from_self(count..self.input_len());

        // we sould not lose any data
        assert_eq!(first.input_len(), count);
        assert_eq!(second.input_len(), self.input_len() - count);
        assert_eq!(first.input_len() + second.input_len(), self.input_len());

        // return the second before the first.
        (second, first)
    }
}

/// Implementation of the [nom::Slice]  ([RangeFull]) trait for [TokenStream]
impl Slice<RangeFull> for TokenStream {
    /// Slices self according to the range argument
    ///
    /// # Panics
    ///
    /// The function panics if the supplied end range exceeds the current
    /// input length of SourcePos.
    #[inline]
    fn slice(&self, _: RangeFull) -> Self {
        // return a clone of our selves
        self.clone()
    }
}

/// Implementation of the [nom::Slice]  ([Range]) trait for [TokenStream]
impl Slice<Range<usize>> for TokenStream {
    /// Slices self according to the range argument
    ///
    /// # Panics
    ///
    /// The function panics if the supplied end range exceeds the current
    /// input length of SourcePos.
    #[inline]
    fn slice(&self, range: Range<usize>) -> Self {
        assert!(range.end <= self.input_len());
        self.from_self(range)
    }
}

/// Implementation of the [nom::Slice]  ([RangeTo]) trait for [TokenStream]
impl Slice<RangeTo<usize>> for TokenStream {
    /// Slices self according to the range argument
    ///
    /// # Panics
    ///
    /// The function panics if the supplied end range exceeds the current
    /// input length of SourcePos.
    #[inline]
    fn slice(&self, range: RangeTo<usize>) -> Self {
        // just return the range from 0..end
        self.slice(0..range.end)
    }
}

/// Implementation of the [nom::Slice]  ([RangeFrom]) trait for [TokenStream]
impl Slice<RangeFrom<usize>> for TokenStream {
    /// Slices self according to the range argument
    ///
    /// # Panics
    ///
    /// The function panics if the supplied end range exceeds the current
    /// input length of SourcePos.
    #[inline]
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        // just return the range from start..end
        self.slice(range.start..self.input_len())
    }
}

/// Represents an iterator over the TokenStream elements
pub struct TokenStreamIter {
    /// A reference to the backing vector of tokens
    content: Rc<Vec<Token>>,

    /// The current valid range of the iterator, the next element is given by [range.start]
    range: Range<usize>,
}

/// Implementation of the TokenStream iterator.
impl TokenStreamIter {
    /// Creates a new TokenStreamIter iterator
    ///
    /// # Panic
    ///
    /// The function will panic if the supplied range is outside backing content
    pub fn new(content: Rc<Vec<Token>>, range: Range<usize>) -> Self {
        assert!(content.len() < range.end);
        TokenStreamIter { content, range }
    }
}

/// Implementation of the [std::iter::Iterator] trait for TokenStreamIter
impl Iterator for TokenStreamIter {
    /// The type of the element is a [Token]
    type Item = Token;

    /// Advances the iterator and returns the next value.
    ///
    /// Returns [`None`] when iteration is finished.
    fn next(&mut self) -> Option<Self::Item> {
        // range is empty <--> iterator is finished.
        if !self.range.is_empty() {
            // record start and bump start value
            let s = self.range.start;
            self.range.start += 1;
            // construct the token value
            Some(self.content[s].clone())
        } else {
            None
        }
    }
}

/// Represents the TokenStreamIndices iterator
pub struct TokenStreamIndices {
    /// A reference to the backing vector of tokens
    content: Rc<Vec<Token>>,

    /// The current valid range of the iterator, the next element is given by [range.start]
    range: Range<usize>,

    /// records the start index of this iterator
    start: usize,
}

/// Implementation of the TokenStreamIndices iterator
impl TokenStreamIndices {
    /// Creates a new TokenStreamIndices iterator
    ///
    /// # Panic
    ///
    /// The function will panic if the supplied range is outside backing content
    pub fn new(content: Rc<Vec<Token>>, range: Range<usize>) -> Self {
        assert!(content.len() < range.end);
        let start = range.start;
        TokenStreamIndices {
            content,
            range,
            start,
        }
    }
}

/// Implementation of the [std::iter::Iterator] trait for TokenStreamIndices
impl Iterator for TokenStreamIndices {
    /// Item type is a tuple of the index and the [Token] at this index
    type Item = (usize, Token);

    /// Advances the iterator and returns the next value.
    ///
    /// Returns [`None`] when iteration is finished.
    fn next(&mut self) -> Option<Self::Item> {
        // range is empty <--> iterator is finished.
        if !self.range.is_empty() {
            let s = self.range.start;
            self.range.start += 1;
            // construct the index and the element
            Some((s - self.start, self.content[s].clone()))
        } else {
            None
        }
    }
}

/// Implements the [nom::InputIter] trait for [TokenStream]
impl InputIter for TokenStream {
    /// The current input type is a sequence of that Item type.
    type Item = Token;

    /// An iterator over the input type, producing the item and its position for use with Slice.
    type Iter = TokenStreamIndices;

    /// An iterator over the input type, producing the item
    type IterElem = TokenStreamIter;

    /// Returns an iterator over the elements and their byte offsets
    #[inline]
    fn iter_indices(&self) -> Self::Iter {
        TokenStreamIndices::new(self.tokens.clone(), self.range.clone())
    }

    /// Returns an iterator over the elements
    #[inline]
    fn iter_elements(&self) -> Self::IterElem {
        TokenStreamIter::new(self.tokens.clone(), self.range.clone())
    }

    /// Finds the byte position of the element
    #[inline]
    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.tokens.iter().position(|b| predicate(b.clone()))
    }

    /// Get the byte offset from the element's position in the stream
    #[inline]
    fn slice_index(&self, count: usize) -> Result<usize, Needed> {
        if self.input_len() >= count {
            Ok(count)
        } else {
            Err(Needed::Unknown)
        }
    }
}
