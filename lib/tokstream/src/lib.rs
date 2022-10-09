// Token Stream Library
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

//! Token Stream Definition
//!
//! The TokenStream represents a sequence of tokens produced by the lexer.
//! It does not contain any whitespace tokens, but may contain comment
//! tokens. Comment tokens can be filtered using the provided functionality.

// used standard library functionality
use std::cmp::PartialEq;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};
use std::rc::Rc;

// external dependencies
use nom::{InputIter, InputLength, InputTake, Needed, Slice};
pub use srcspan::{SrcLoc, SrcSpan};

// crate modules
mod token;
pub use token::{Token, TokenKind};

/// Represents a sequence of tokens
#[derive(Clone, PartialEq, Eq)]
pub struct TokenStream<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// a reference counted vector of tokens
    tokens: Rc<Vec<Token<T>>>,

    /// Holds the valid range within the [Token] vector
    range: Range<usize>,

    /// The source span of the current range of the [TokenStream]
    span: SrcSpan,
}

impl<T> TokenStream<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// Creates a new [TokenStream] from the given vector of tokens
    pub fn new(tokens: Vec<Token<T>>) -> Self {
        let len = tokens.len();

        let span = if tokens.is_empty() {
            SrcSpan::empty()
        } else {
            let mut span = tokens[0].span().clone();
            span.expand_until_end(tokens[len - 1].span());
            span
        };

        TokenStream {
            tokens: Rc::new(tokens),
            range: 0..len,
            span,
        }
    }

    /// Creates a new [TokenStream] from the given vector of tokens
    pub fn new_filtered(mut tokens: Vec<Token<T>>) -> Self {
        // filter tokens that do not match the predicated
        tokens.retain(|t| t.keep());
        Self::new(tokens)
    }

    /// Creates an empty [TokenStream]
    pub fn empty() -> Self {
        Self::new(Vec::new())
    }

    /// Filters out all tokens not matching the supplied predicated
    ///
    /// If there are multiple references to the underlying token stream
    /// then this will clone the vector of the tokens, otherwise it will
    /// just filter the existing vector in place retaining elements that
    /// match the provided predicate.
    pub fn with_retained<F>(self, pred: F) -> Self
    where
        F: Fn(&Token<T>) -> bool,
    {
        let mut tokens = Rc::try_unwrap(self.tokens).unwrap_or_else(|rc| (*rc).clone());
        tokens.retain(|t| pred(t));
        TokenStream::new(tokens)
    }

    /// Constructs a new [TokenStream] covering a subrange of [self]
    ///
    /// This will construct a new  [TokenStream] object with updated range.
    ///
    /// # Arguments
    ///
    /// * `range` - The subrange of the new  [TokenStream] within the current  [TokenStream]
    ///
    /// # Panics
    ///
    /// Panics if the supplied range is outside of the covered range by the  [TokenStream]
    pub fn from_self_with_subrange(&self, range: Range<usize>) -> Self {
        if self.len() < range.end {
            panic!("Cannot create subrange outside of the current range");
        }

        // clone the current span
        let mut newstream = self.clone();

        // move cursor to the start of the desired span
        for _ in 0..range.start {
            newstream.pos_next();
        }
        // update the end of the new span
        newstream.range.end = self.range.start + range.end;
        assert!(newstream.len() == range.end - range.start);

        newstream
    }

    pub fn from_self_until_end(&self, other: &Self) -> Self {
        let mut newstream = self.clone();
        newstream.span_until_end(other);
        newstream
    }

    pub fn from_self_until_start(&self, other: &Self) -> Self {
        let mut newstream = self.clone();
        newstream.span_until_end(other);
        newstream
    }

    /// Expands [self] to cover everything until but not including `pos`
    ///
    /// The new TokenStream will have the same starting position as self.
    /// but with an increased length up to but not including `pos`
    ///
    /// Note, this will not shrink `self` if `pos` is before the end of `self`
    ///
    /// # Arguments
    ///
    ///  * `pos` - The position to expand to
    ///
    /// # Panics
    ///
    ///  * If the new end position would be before the current start
    pub fn expand_until(&mut self, pos: usize) {
        if pos < self.range.start {
            panic!("Cannot expand before to the current start of TokenStream. ");
        }

        // don't expand beyond the end of the valid range
        let pos = std::cmp::min(pos, self.tokens.len());

        // update if we are actually expanding
        if self.range.end <= pos {
            self.range.end = pos;
            self.update_span();
        }
    }

    /// Expands [self] to cover everything until the start of `other`
    ///
    /// The new TokenStream will have the same starting position as self.
    /// but with an increased length up to but not including the other one.
    ///
    /// Note, this will not shrink `self` if the start of `other` is before
    /// the end of `self.
    ///
    /// # Arguments
    ///
    ///  * `other` - The other TokenStream to expand to
    ///
    /// # Panics
    ///
    ///  * If the two TokenStreams are not related.
    ///  * If the new end position would be before the current start
    pub fn expand_until_start(&mut self, other: &Self) {
        if self.tokens != other.tokens {
            panic!("Cannot expand TokenStream to unrelated TokenStream");
        }

        self.expand_until(other.range.start);
    }

    /// Expands [self] to cover everything until the end of `other`
    ///
    /// Note, this will not shrink `self` if the start of `other` is before
    /// the end of `self.
    ///
    /// # Arguments
    ///
    ///  * `other` - The other TokenStream to expand to
    ///
    /// # Panics
    ///
    ///  * If the two TokenStreams are not related.
    ///  * If the new end position would be before the current start
    pub fn expand_until_end(&mut self, other: &Self) {
        if self.tokens != other.tokens {
            panic!("Cannot expand TokenStream to unrelated TokenStream");
        }

        self.expand_until(other.range.end);
    }

    /// Adjusts [self] to cover everything until `pos`
    ///
    /// The new TokenStream will have the same starting position as self.and an
    /// adjusted length up to bu not including `pos`. This may shrink the current`
    /// TokenStream
    ///
    /// # Arguments
    ///
    ///  * `pos` - Then position to adjust the span to
    ///
    /// # Panics
    ///
    ///  * If the new end position would be before the current start
    pub fn span_until(&mut self, pos: usize) {
        if pos < self.range.start {
            panic!("Cannot span before to the current start of TokenStream. ");
        }

        // don't expand beyond the end of the valid range
        let pos = std::cmp::min(pos, self.tokens.len());

        self.range.end = pos;
        self.update_span();
    }

    /// Adjusts [self] to cover everything until the start of `other`
    ///
    /// The new TokenStream will have the same starting position as self.
    /// but with an increased length up to but not including the other one.
    /// This may shrink or expand the current span.
    ///
    /// # Arguments
    ///
    ///  * `other` - The other TokenStream to expand to
    ///
    /// # Panics
    ///
    ///  * If the two TokenStreams are not related.
    ///  * If the new end position would be before the current start
    pub fn span_until_start(&mut self, other: &Self) {
        if self.tokens != other.tokens {
            panic!("Cannot span TokenStream to unrelated TokenStream");
        }

        self.span_until(other.range.start);
    }

    /// Adjusts [self] to cover everything until the end of `other`
    ///
    /// The new TokenStream will have the same starting position as self.
    /// but with an increased length up to but not including the other one.
    /// This may shrink or expand the current span.
    ///
    /// # Arguments
    ///
    ///  * `other` - The other TokenStream to span to
    ///
    /// # Panics
    ///
    ///  * If the two TokenStreams are not related.
    ///  * If the new end position would be before the current start
    pub fn span_until_end(&mut self, other: &Self) {
        if self.tokens != other.tokens {
            panic!("Cannot span TokenStream to unrelated TokenStream");
        }

        self.span_until(other.range.end);
    }

    /// Obtains a string slice to the entire source of the [SrcSpan]
    pub fn tokens(&self) -> &[Token<T>] {
        self.tokens.as_ref()
    }

    pub fn len(&self) -> usize {
        self.range.end - self.range.start
    }

    /// Checks whether this [TokenStream] is empty, i.e., covers an empty range.
    pub fn is_empty(&self) -> bool {
        self.range.is_empty()
    }

    /// Checks whether the position of this [SrcSpan] is at the end of the source
    pub fn is_eof(&self) -> bool {
        self.range.end == self.tokens.len()
    }

    /// Returns the current range within the source for this SrcSpan.
    ///
    /// The range defines the current slice of the input content this SrcSpan represents.
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }

    /// Updates the current span
    fn update_span(&mut self) {
        if self.range.start == self.tokens.len() {
            // we've reached the end of the input, adjust
            while !self.span.is_empty() {
                self.span.pos_next()
            }
        } else {
            let span = self.tokens[self.range.start].span();
            if self.span.starts_with(span) {
                // the current span starts with the start token, so just expand
                self.span
                    .span_until_end(self.tokens[self.range.end - 1].span());
            } else {
                // we don't have a common start, so replace the span.
                let mut span = self.tokens[self.range.start].span().clone();
                span.span_until_end(self.tokens[self.range.end - 1].span());
                self.span = span;
            }
        }
    }

    /// Moves the position to the next char of the SrcSpan.
    ///
    /// This shrinks the range of the SrcSpan to not include the next char anymore.
    pub fn pos_next(&mut self) {
        if self.is_empty() {
            return;
        }

        self.range.start += 1;
        self.update_span();
    }

    /// Moves the position to the previous char of the source.
    ///
    /// This expands the current source span to include the previous char.
    pub fn pos_prev(&mut self) {
        if self.range.start == 0 {
            return;
        }

        self.range.start -= 1;
        self.update_span();
    }

    /// Moves the position to the first token of the next line in the source
    pub fn pos_next_line(&mut self) {
        // let currentline = self.line;
        // while !self.is_empty() && self.line == currentline {
        //     self.pos_next();
        // }
    }

    /// Moves the position to the first token of previous line in the source
    pub fn pos_prev_line(&mut self) {
        // let currentline = self.line;
        // while self.range.start > 0 && self.line == currentline {
        //     self.pos_prev();
        // }
    }

    /// Returns the current tokens within the range as a slice
    pub fn as_slice(&self) -> &[Token<T>] {
        &self.tokens[self.range.clone()]
    }

    /// Returns the first token of this [TokenStream]
    pub fn peek(&self) -> Option<&Token<T>> {
        if self.is_empty() {
            None
        } else {
            Some(&self.tokens[self.range.start])
        }
    }

    /// Returns the last token of this [TokenStream]
    pub fn last(&self) -> Option<&Token<T>> {
        if self.is_empty() {
            None
        } else {
            Some(&self.tokens[self.range.end - 1])
        }
    }

    /// obtain the [SrcSpan] covering the entire token range
    pub fn span(&self) -> &SrcSpan {
        &self.span
    }

    /// Returns the [SrcSpan] utnil the other [TokenStream] starts
    ///
    /// # Panics
    ///
    ///  The function panics if the two TokenStreams are not related
    pub fn to_span_until_start(&self, other: &Self) -> SrcSpan {
        if self.tokens != other.tokens {
            panic!("Cannot expand TokenStream to unrelated TokenStream");
        }

        let mut span = self.span.clone();
        span.expand_until_start(other.span());
        span
    }

    /// Obtains the location of the current first token in the stream.
    pub fn loc(&self) -> &SrcLoc {
        self.span.loc()
    }
}

/// Implements the [Display] trait for [TokenStream]
impl<T> Display for TokenStream<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        let start = if self.range.start > 5 {
            self.range.start - 5
        } else {
            0
        };

        let end = std::cmp::min(self.range.end + 5, self.tokens.len());

        if start == 0 {
            writeln!(f, "      [     ]  <start-of-file>")?;
        } else {
            writeln!(f, "      [     ]  ...")?;
        }

        for i in start..end {
            let t = &self.tokens[i];
            if i == self.range.start {
                writeln!(f, " ---> [{:>5}]  {}", i, t)?;
            } else {
                writeln!(f, "      [{:>5}]  {}", i, t)?;
            }
        }

        if start == end {
            writeln!(f, " ---> <NO TOKENS>")?;
        }

        if end == self.tokens.len() {
            writeln!(f, "      [     ]  <end-of-file>")
        } else {
            writeln!(f, "      [     ]  ...")
        }
    }
}

/// Implements the [Debug] trait for [TokenStream]
impl<T> Debug for TokenStream<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        writeln!(f, "      [     ]  <start-of-file>")?;
        for (i, t) in self.tokens.iter().enumerate() {
            if i == self.range.start {
                writeln!(f, " ---> {:>5}  {}", i, t)?;
            } else {
                writeln!(f, "      {:>5}  {}", i, t)?;
            }
        }
        writeln!(f, "      [     ]  <end-of-file>")
    }
}

impl<T> Default for TokenStream<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    fn default() -> Self {
        Self::new(Vec::new())
    }
}

/// Implementation of the [nom::InputLength] trait for [TokenStream]
impl<T> InputLength for TokenStream<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    #[inline]
    /// Calculates the input length, as indicated by its name, and the name of the trait itself
    fn input_len(&self) -> usize {
        self.len()
    }
}

/// Implementation of the [nom::InputTake] trait for [TokenStream]
impl<T> InputTake for TokenStream<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    #[inline]
    /// Returns a new [TokenStream] covering the first `count` tokens.
    ///
    /// # Panics
    ///
    /// The function panics if count > self.input_len()
    fn take(&self, count: usize) -> Self {
        assert!(count <= self.input_len());
        self.from_self_with_subrange(0..count)
    }

    #[inline]
    /// Split the [TokenStream] at the `count` tokens.
    ///
    /// # Panics
    /// The function panics if count > self.input_len()
    fn take_split(&self, count: usize) -> (Self, Self) {
        assert!(count <= self.input_len());

        let first = self.from_self_with_subrange(0..count);
        let second = self.from_self_with_subrange(count..self.input_len());

        // we sould not lose any data
        assert_eq!(first.input_len(), count);
        assert_eq!(second.input_len(), self.input_len() - count);
        assert_eq!(first.input_len() + second.input_len(), self.input_len());

        // return the second before the first.
        (second, first)
    }
}

/// Implementation of the [nom::Slice]  ([RangeFull]) trait for [TokenStream]
impl<T> Slice<RangeFull> for TokenStream<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// Slices self according to the range argument
    #[inline]
    fn slice(&self, _: RangeFull) -> Self {
        // return a clone of our selves
        self.clone()
    }
}

/// Implementation of the [nom::Slice]  ([Range]) trait for [TokenStream]
impl<T> Slice<Range<usize>> for TokenStream<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// Slices self according to the range argument
    ///
    /// # Panics
    ///
    /// The function panics if the supplied end range exceeds the current
    /// input length of TokenStream.
    #[inline]
    fn slice(&self, range: Range<usize>) -> Self {
        self.from_self_with_subrange(range)
    }
}

/// Implementation of the [nom::Slice]  ([RangeTo]) trait for [TokenStream]
impl<T> Slice<RangeTo<usize>> for TokenStream<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// Slices self according to the range argument
    ///
    /// # Panics
    ///
    /// The function panics if the supplied end range exceeds the current
    /// input length of TokenStream.
    #[inline]
    fn slice(&self, range: RangeTo<usize>) -> Self {
        self.slice(0..range.end)
    }
}

/// Implementation of the [nom::Slice]  ([RangeFrom]) trait for [TokenStream]
impl<T> Slice<RangeFrom<usize>> for TokenStream<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// Slices self according to the range argument
    ///
    /// # Panics
    ///
    /// The function panics if the supplied end range exceeds the current
    /// input length of TokenStream.
    #[inline]
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        // just return the range from start..end
        self.slice(range.start..self.len())
    }
}

/// Represents an iterator over the TokenStream elements
pub struct TokenStreamIter<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// A reference to the backing vector of tokens
    content: Rc<Vec<Token<T>>>,

    /// The current valid range of the iterator, the next element is given by [range.start]
    range: Range<usize>,
}

/// Implementation of the TokenStream iterator.
impl<T> TokenStreamIter<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// Creates a new TokenStreamIter iterator
    ///
    /// # Panic
    ///
    /// The function will panic if the supplied range is outside backing content
    pub fn new(content: Rc<Vec<Token<T>>>, range: Range<usize>) -> Self {
        assert!(content.len() < range.end);
        TokenStreamIter { content, range }
    }
}

/// Implementation of the [std::iter::Iterator] trait for TokenStreamIter
impl<T> Iterator for TokenStreamIter<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// The type of the element is a [Token]
    type Item = Token<T>;

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
pub struct TokenStreamIndices<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// A reference to the backing vector of tokens
    content: Rc<Vec<Token<T>>>,

    /// The current valid range of the iterator, the next element is given by [range.start]
    range: Range<usize>,

    /// records the start index of this iterator
    start: usize,
}

/// Implementation of the TokenStreamIndices iterator
impl<T> TokenStreamIndices<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// Creates a new TokenStreamIndices iterator
    ///
    /// # Panic
    ///
    /// The function will panic if the supplied range is outside backing content
    pub fn new(content: Rc<Vec<Token<T>>>, range: Range<usize>) -> Self {
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
impl<T> Iterator for TokenStreamIndices<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// Item type is a tuple of the index and the [Token] at this index
    type Item = (usize, Token<T>);

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
impl<T> InputIter for TokenStream<T>
where
    T: TokenKind + Display + PartialEq + Clone,
{
    /// The current input type is a sequence of that Item type.
    type Item = Token<T>;

    /// An iterator over the input type, producing the item and its position for use with Slice.
    type Iter = TokenStreamIndices<T>;

    /// An iterator over the input type, producing the item
    type IterElem = TokenStreamIter<T>;

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
        self.as_slice().iter().position(|b| predicate(b.clone()))
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
