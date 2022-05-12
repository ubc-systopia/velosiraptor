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

//! Velosiraptor TokenStream
//!
//! The TokenStream represents a sequence of tokens produced by the lexer.
//! It does not contain any whitespace tokens, but may contain comment
//! tokens. Comment tokens can be filtered using the provided functionality.

// used standard library functionality
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};
use std::rc::Rc;

// used nom functionality
use nom::{InputIter, InputLength, InputTake, Needed, Slice};

// used crate-internal functionality
use crate::error::ErrorLocation;
use crate::sourcepos::SourcePos;
use crate::token::{Token, TokenContent};

/// A sequence of recognized tokens that is produced by the lexer
#[derive(Clone, PartialEq)]
pub struct TokenStream {
    /// a reference counted vector of tokens
    tokens: Option<Rc<Vec<Token>>>,

    /// Holds the valid range within the [Token] vector
    range: Range<usize>,
}

pub const TOKENSTREAM_DUMMY: TokenStream = TokenStream {
    tokens: None,
    range: 0..0,
};

/// Implementation of the [TokenStream]
impl TokenStream {
    /// Creates a new TokenStream from the supplied vector of tokens
    ///
    /// The TokenStream will cover the entire vector.
    pub fn from_vec(tokens: Vec<Token>) -> Self {
        let len = tokens.len();
        TokenStream {
            tokens: Some(Rc::new(tokens)),
            range: 0..len,
        }
    }

    pub fn from_vec_filtered(tokens: Vec<Token>) -> Self {
        let tok: Vec<Token> = tokens
            .iter()
            .filter(|t| {
                !matches!(
                    t.content,
                    TokenContent::Comment(_) | TokenContent::BlockComment(_)
                )
            })
            .cloned()
            .collect();
        Self::from_vec(tok)
    }

    /// Creates a new [TokenStream] from the supplied [Token] slice.empty()
    ///
    /// This will create a new vector of Tokens from the supplied slice.
    pub fn from_slice(tokens: &[Token]) -> Self {
        Self::from_vec(tokens.to_vec())
    }

    /// Creates a new [TokenStream] covering a subrange of [self]
    ///
    /// # Panics
    ///
    /// Panics if the supplied range is outside of the covered range by the [TokenStream]
    pub fn with_range(&self, range: Range<usize>) -> Self {
        assert!(self.input_len() >= range.end - range.start);
        assert!(self.range.start + range.end <= self.range.end);

        // the new range is the supplied range, shifted by the current range
        let range = self.range.start + range.start..self.range.start + range.end;

        TokenStream {
            tokens: self.tokens.clone(),
            range,
        }
    }

    /// Creates a new [TokenStream] from self up until, not including the other
    ///
    /// The new range will start at current, and be set to the token just before
    /// the start of the other TokenStream
    ///
    /// # Panics
    ///
    /// The function panics if the tokens are not matching, or the end is before the start
    pub fn expand_until(self, other: &Self) -> Self {
        assert!(self.tokens == other.tokens);
        assert!(self.range.start < other.range.start);
        TokenStream {
            tokens: self.tokens,
            range: self.range.start..other.range.start,
        }
    }

    /// Creates a new [TokenStream] from self up until, and including the other
    ///
    /// The new range will start at current, and be set to the token just before
    /// the start of the other TokenStream
    ///
    /// # Panics
    ///
    /// The function panics if the tokens are not matching, or the end is before the start
    pub fn merge(self, other: &Self) -> Self {
        assert!(self.tokens == other.tokens);
        assert!(self.range.start < other.range.end);
        TokenStream {
            tokens: self.tokens,
            range: self.range.start..other.range.end,
        }
    }

    /// Creates an empty TokenStream.
    pub fn empty() -> Self {
        TokenStream {
            tokens: None,
            range: 0..0,
        }
    }

    /// Returns true if this TokenStream is empty
    pub fn is_empty(&self) -> bool {
        self.range.is_empty()
    }

    /// Returns true if the current token is the end-of-file token
    pub fn is_eof(&self) -> bool {
        assert_eq!(
            self.input_len() == 1,
            self.peek().content == TokenContent::Eof
        );
        self.input_len() == 1
    }

    /// Returns the current slice of Tokens backed by this [TokenStream]
    pub fn as_slice(&self) -> &[Token] {
        self.tokens.as_ref().unwrap().as_slice()
    }

    /// Returns the first [Token] in the [TokenStream]
    pub fn peek(&self) -> &Token {
        assert!(!self.is_empty());
        assert!(self.tokens.is_some());
        &self.tokens.as_ref().unwrap()[self.range.start]
    }

    pub fn last(&self) -> &Token {
        assert!(!self.is_empty());
        assert!(self.tokens.is_some());
        &self.tokens.as_ref().unwrap()[self.range.end - 1]
    }

    /// Obtains the [SourcePos] of the current [Token] in the [TokenStream]
    pub fn input_sourcepos(&self) -> SourcePos {
        let start = self.peek().spos.clone();
        let end = &self.last().spos;
        start.from_self_merged(end)
    }

    /// Calculates the sourcepos span between two tokenstreams
    pub fn input_sourcepos_span(&self, other: &TokenStream) -> SourcePos {
        assert!(self.tokens == other.tokens);
        assert!(self.range.start <= other.range.start);
        self.input_sourcepos()
            .expand_until(&other.input_sourcepos())
    }

    /// Obtains the current range relative to the entire [TokenStream]
    pub fn input_range(&self) -> Range<usize> {
        self.range.clone()
    }

    /// Returns a slice covering the entire input tokens.
    pub fn input_tokens(&self) -> &[Token] {
        match &self.tokens {
            Some(tokens) => &tokens[..],
            None => &[],
        }
    }

    /// returns a string with the position information
    pub fn location(&self) -> String {
        format!("{}:{}:{}", self.context(), self.line(), self.column())
    }
}

/// Implements the [Display] trait for [TokenStream]
impl Display for TokenStream {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match &self.tokens {
            Some(tokens) => write!(f, "{}", tokens[self.range.start]),
            None => write!(f, "No Tokens",),
        }
    }
}

/// Implements the [Debug] trait for [TokenStream]
impl Debug for TokenStream {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        let len = std::cmp::min(self.input_len(), 5);
        let mut tok = String::new();
        match &self.tokens {
            Some(tokens) => {
                for i in &tokens[self.range.start..self.range.start + len] {
                    tok.push_str(&format!("    - {}\n", i))
                }
            }
            None => tok.push_str("No Tokens"),
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
        self.with_range(0..count)
    }

    #[inline]
    /// Split the [TokenStream] at the `count` tokens.
    ///
    /// # Panics
    /// The function panics if count > self.input_len()
    fn take_split(&self, count: usize) -> (Self, Self) {
        assert!(count <= self.input_len());

        let first = self.with_range(0..count);
        let second = self.with_range(count..self.input_len());

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
        self.with_range(range)
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
        match &self.tokens {
            Some(tokens) => TokenStreamIndices::new(tokens.clone(), self.range.clone()),
            None => TokenStreamIndices::new(Rc::new(Vec::new()), self.range.clone()),
        }
    }

    /// Returns an iterator over the elements
    #[inline]
    fn iter_elements(&self) -> Self::IterElem {
        match &self.tokens {
            Some(tokens) => TokenStreamIter::new(tokens.clone(), self.range.clone()),
            None => TokenStreamIter::new(Rc::new(Vec::new()), self.range.clone()),
        }
    }

    /// Finds the byte position of the element
    #[inline]
    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        match &self.tokens {
            Some(t) => t[self.range.clone()]
                .iter()
                .position(|b| predicate(b.clone())),
            None => None,
        }
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

/// Implementation of the [error::ErrorLocation] trait for [TokenStream]
impl ErrorLocation for TokenStream {
    /// the line number in the source file
    fn line(&self) -> u32 {
        self.peek().spos.line()
    }

    /// the column number in the source file
    fn column(&self) -> u32 {
        self.peek().spos.column()
    }

    /// the length of the token
    fn length(&self) -> usize {
        // TODO: figure out the right thing here!
        self.peek().spos.length()
    }

    /// the context (stdin or filename)
    fn context(&self) -> &str {
        self.peek().spos.context()
    }

    /// the surrounding line context
    fn linecontext(&self) -> &str {
        self.peek().spos.linecontext()
    }
}

/// Implementation of the [error::ErrorLocation] trait for [TokenStream]
impl ErrorLocation for &TokenStream {
    /// the line number in the source file
    fn line(&self) -> u32 {
        self.peek().spos.line()
    }

    /// the column number in the source file
    fn column(&self) -> u32 {
        self.peek().spos.column()
    }

    /// the length of the token
    fn length(&self) -> usize {
        // TODO: figure out the right thing here!
        self.input_sourcepos().length()
    }

    /// the context (stdin or filename)
    fn context(&self) -> &str {
        self.peek().spos.context()
    }

    /// the surrounding line context
    fn linecontext(&self) -> &str {
        self.peek().spos.linecontext()
    }
}

/// Implementation of [std::convert::From<LexerError>] for [VrsError]
///
/// This converts from a lexer error to a parser error
impl From<SourcePos> for TokenStream {
    fn from(spos: SourcePos) -> Self {
        TokenStream {
            tokens: Some(Rc::new(vec![Token {
                content: TokenContent::Illegal,
                spos,
            }])),
            range: 0..0,
        }
    }
}

/// implementation of [PartialOrd] for [TokenStream]
impl PartialOrd for TokenStream {
    /// This method returns an ordering between self and other values if one exists.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // we jus compare with the head token position
        self.peek().spos.partial_cmp(&other.peek().spos)
    }
}
