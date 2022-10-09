// Source Span Library
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

//! # The SrcSpan definition
//!
//! The SrcSpan is a structure containing information about the source file / string
//! that has been parsed. It represents a recognized range of the source file, including
//! its meta information such as the position within the source file.
//!
//! The SrcSpan structure implements several traits used by Nom so we can simply pass
//! the SrcSpan struct as input/outputs.

// Standard library imports
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};
use std::rc::Rc;

// modules
mod loc;

// public re-exports
pub use loc::SrcLoc;

// used nom functionality
use nom::{
    error::{ErrorKind, ParseError},
    Compare, CompareResult, Err, FindSubstring, IResult, InputIter, InputLength, InputTake,
    InputTakeAtPosition, Needed, Offset, Slice,
};

/// Corresponds to a single byte of the source file
pub type Element = char;

/// The SrcSpan tracks the position and content of the string to be lexed
///
/// This structures keeps track of the context (e.g., file name) as well as the
/// current range of the SrcSpan within the context as a range of characters in content string.
/// Moreover, we keep track on the line and column.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct SrcSpan {
    /// Content this source span covers.
    content: Rc<String>,

    /// Holds the valid range within the `content` string
    range: Range<usize>,

    /// Location within the source file
    loc: SrcLoc,
}

/// The SrcSpan implemetation
impl SrcSpan {
    /// Creates a new SrcSpan with a given input.
    ///
    /// The meta data of the SrcSpan is initialized with the default values:
    ///  - it will start at line 1, column 1
    ///  - the range will cover the entire content
    ///  - the context will be set to None
    ///
    /// # Arguments
    ///
    /// * `content` - A string representing the content of the SrcSpan
    ///
    /// # Panics
    ///
    /// The function panics if the supplied string is non-ascii.
    pub fn new(content: String) -> Self {
        if !content.is_ascii() {
            panic!("SrcSpan only supports ASCII strings");
        }

        for c in content.chars() {
            if c > 126 as char && c < 32 as char && c != '\n' {
                panic!("SrcSpan only supports ASCII strings: {:x}", c as u32);
            }
        }

        // TODO: maybe filter some of the non-printable characters out here?
        let len = content.len();
        SrcSpan {
            content: Rc::new(content),
            range: 0..len,
            loc: SrcLoc::new(),
        }
    }

    /// Creates a new SrcSpan with a given input.
    ///
    /// The meta data of the SrcSpan is initialized with the default values:
    ///  - it will start at line 1, column 1
    ///  - the range will cover the entire content
    ///
    /// # Arguments
    ///
    /// * `content` - A string representing the content of the SrcSpan
    /// * `context` - A string representing the context of the SrcSpan
    ///
    /// # Panics
    ///
    /// The function panics if the supplied string is non-ascii.
    pub fn with_context(content: String, context: String) -> Self {
        let mut span = SrcSpan::new(content);
        span.loc.set_context(context);
        span
    }

    /// Creates an empty SrcSpan
    ///
    /// This is equivalent to `SrcSpan::new(String::new())`
    pub fn empty() -> Self {
        Self::from("")
    }

    /// Constructs a new SrcSpan covering a subrange of [self]
    ///
    /// This will construct a new SrcSpan object with updated range, columns and lines,
    /// but with the same context and content.
    ///
    /// # Arguments
    ///
    /// * `range` - The subrange of the new SrcSpan within the current [SrcSpan]
    ///
    /// # Panics
    ///
    /// Panics if the supplied range is outside of the covered range by the [SrcSpan]
    pub fn from_self_with_subrange(&self, range: Range<usize>) -> Self {
        if self.len() < range.end {
            panic!("Cannot create subrange outside of the current range");
        }

        // clone the current span
        let mut newspan = self.clone();

        // move cursor to the start of the desired span
        for _ in 0..range.start {
            newspan.pos_next();
        }
        // update the end of the new span
        newspan.range.end = self.range.start + range.end;
        assert!(newspan.len() == range.end - range.start);

        newspan
    }

    /// Expands [self] to cover everything until but not including `pos`
    ///
    /// The new source position will have the same starting position as self.
    /// but with an increased length up to but not including `pos.
    ///
    /// Note, this will not shrink the span if `pos` is before the end of `self`
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
            panic!("Cannot expand before to the current start of SrcSpan.");
        }

        // don't expand beyond the end of the valid range
        let pos = std::cmp::min(pos, self.content.len());

        // update if we are actually expanding
        if self.range.end <= pos {
            self.range.end = pos;
        }
    }

    /// Expands [self] to cover everything until the start of `other`
    ///
    /// The new source position will have the same starting position as self.
    /// but with an increased length up to but not including the other one.
    ///
    /// Note, this will not shrink the span if the start of the other span
    /// is before the end of the current span.
    ///
    /// # Arguments
    ///
    ///  * `other` - The other SrcSpan to expand to
    ///
    /// # Panics
    ///
    ///  * If the two SrcSpan are not related.
    ///  * If the new end position would be before the current start
    pub fn expand_until_start(&mut self, other: &Self) {
        if self.loc.context() != other.loc.context() || self.content != other.content {
            panic!("Cannot expand SrcSpan to unrelated SrcSpan");
        }

        self.expand_until(other.range.start);
    }

    /// Expands [self] to cover everything until the end of `other`
    ///
    /// The new source position will have the same starting position as self.
    /// but with an increased length up to and including the other one.
    ///
    /// Note, this will not shrink the span if the start of the other span
    /// is before the end of the current span.
    ///
    /// # Arguments
    ///
    ///  * `other` - The other SrcSpan to expand to
    ///
    /// # Panics
    ///
    ///  * If the two SrcSpan are not related.
    ///  * If the other SrcSpan is not after the current one.
    pub fn expand_until_end(&mut self, other: &Self) {
        if self.loc.context() != other.loc.context() || self.content != other.content {
            panic!("Cannot expand SrcSpan to unrelated SrcSpan");
        }

        self.expand_until(other.range.end);
    }

    /// Adjusts [self] to cover everything until but not including `pos`
    ///
    /// The new source position will have the same starting position as self.
    /// but with an increased length up to but not including `pos. This may shrink
    /// the current SrcSpan.
    ///
    /// # Arguments
    ///
    ///  * `pos` - The position to expand to
    ///
    /// # Panics
    ///
    ///  * If the new end position would be before the current start
    pub fn span_until(&mut self, pos: usize) {
        if pos < self.range.start {
            panic!("Cannot expand before to the current start of SrcSpan.");
        }

        // don't expand beyond the end of the valid range
        let pos = std::cmp::min(pos, self.content.len());

        // update if we are actually expanding
        self.range.end = pos;
    }

    /// Adjusts [self] to cover everything until the start of `other`
    ///
    /// The new source position will have the same starting position as self.
    /// but with an increased length up to but not including the other one.
    ///
    /// If the start of the other SrcSpan is before the end of current then
    /// the current will be shrunk.
    ///
    /// # Arguments
    ///
    ///  * `other` - The other SrcSpan to expand to
    ///
    /// # Panics
    ///
    ///  * If the two SrcSpan are not related.
    ///  * If the new end position would be before the current start
    pub fn span_until_start(&mut self, other: &Self) {
        if self.loc.context() != other.loc.context() || self.content != other.content {
            panic!("Cannot span SrcSpan to unrelated SrcSpan");
        }

        self.span_until(other.range.start);
    }

    /// Expands [self] to cover everything until the end of `other`
    ///
    /// The new source position will have the same starting position as self.
    /// but with an increased length up to and including the other one.
    ///
    /// If the start of the other SrcSpan is before the end of current then
    /// the current will be shrunk.
    ///
    /// # Arguments
    ///
    ///  * `other` - The other SrcSpan to expand to
    ///
    /// # Panics
    ///
    ///  * If the two SrcSpan are not related.
    ///  * If the other SrcSpan is not after the current one.
    pub fn span_until_end(&mut self, other: &Self) {
        if self.loc.context() != other.loc.context() || self.content != other.content {
            panic!("Cannot span SrcSpan to unrelated SrcSpan");
        }

        self.span_until(other.range.end);
    }

    /// Sets the context of the [SrcSpan]
    pub fn set_context(&mut self, context: String) {
        self.loc.set_context(context);
    }

    /// Obtains a reference to the context of the [SrcSpan]
    pub fn context(&self) -> Option<&str> {
        self.loc.context()
    }

    /// Obtains a string slice to the entire source of the [SrcSpan]
    pub fn content(&self) -> &str {
        &self.content
    }

    /// Obtains the source line for the current position
    pub fn srcline(&self) -> &str {
        // find the start of the current line.
        let mut start = self.range.start;
        for c in self.content[0..start].chars().rev() {
            if c as char == '\n' || start == 0 {
                break;
            }
            start -= 1;
        }
        // discard the newline character, if any
        if self.content[start..].starts_with('\n') {
            start += 1;
        }

        // find the end of the line
        let mut end = self.range.start;
        for c in self.content[end..].chars() {
            if c as char == '\n' {
                break;
            }
            end += 1;
        }
        &self.content[start..end]
    }

    /// The length of the source span
    pub fn len(&self) -> usize {
        self.range.end - self.range.start
    }

    /// Obtains the current [SrcLoc] of this SrcSpan in the source
    pub fn loc(&self) -> &SrcLoc {
        &self.loc
    }

    /// Obtains the source line (starting from 1) of the current position within the source
    pub fn line(&self) -> u32 {
        self.loc.line()
    }

    /// Obtains the source column (starting from 1) of the current position within the source
    pub fn column(&self) -> u32 {
        self.loc.column()
    }

    /// Obtains the contents fo the current SrcSpan as a string slice.
    ///
    /// This will return a slice into the content given by the current range.
    pub fn as_str(&self) -> &str {
        &self.content[self.range.clone()]
    }

    /// Checks whether this [SrcSpan] is empty, i.e., covers an empty range.
    pub fn is_empty(&self) -> bool {
        self.range.is_empty()
    }

    /// Checks whether the position of this [SrcSpan] is at the end of the source
    pub fn is_eof(&self) -> bool {
        self.range.end == self.content.len()
    }

    /// Checks whether the the SrcSpan is the default value
    pub fn is_default(&self) -> bool {
        self.content.is_empty()
    }

    /// Returns the current range within the source for this SrcSpan.
    ///
    /// The range defines the current slice of the input content this SrcSpan represents.
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }

    /// Checks whether the other [SrcSpan] is a prefix of this [SrcSpan]
    pub fn starts_with(&self, other: &Self) -> bool {
        if self.loc.context() != other.loc.context() || self.content != other.content {
            return false;
        }

        if self.range.start != other.range.start {
            return false;
        }

        if self.range.end < other.range.end {
            return false;
        }

        true
    }

    /// Moves the position to the next char of the SrcSpan.
    ///
    /// This shrinks the range of the SrcSpan to not include the next char anymore.
    pub fn pos_next(&mut self) {
        if self.is_empty() {
            return;
        }

        // if the current char is a newline, update the line and column
        if self.as_str().starts_with('\n') {
            self.loc.inc_line(1);
            self.loc.start_of_line();
        } else {
            self.loc.inc_column(1);
        }

        self.range.start += 1;
    }

    /// Moves the position to the previous char of the source.
    ///
    /// This expands the current source span to include the previous char.
    pub fn pos_prev(&mut self) {
        if self.range.start == 0 {
            return;
        }

        self.range.start -= 1;

        // if the current char is a newline, update the line and column
        if self.as_str().starts_with('\n') {
            self.loc.dec_line(1);
            self.loc.start_of_line();
            let prefix = 0..self.range.start;
            for c in self.content[prefix].chars().rev() {
                if c == '\n' {
                    break;
                }
                self.loc.inc_column(1);
            }
        } else {
            self.loc.dec_column(1);
        }
    }

    /// Moves the position to the next line in the source
    pub fn pos_next_line(&mut self) {
        let currentline = self.loc.line();
        while !self.is_empty() && self.loc.line() == currentline {
            self.pos_next();
        }
    }

    /// Moves the position to the previous line in the source
    pub fn pos_prev_line(&mut self) {
        let currentline = self.loc.line();
        while self.range.start > 0 && self.loc.line() == currentline {
            self.pos_prev();
        }
    }
}

/// Implements the [nom::InputLength] trait for [SrcSpan]
impl InputLength for SrcSpan {
    /// Calculates the input length, as indicated by its name, and the name of the trait itself
    fn input_len(&self) -> usize {
        self.len()
    }
}

/// Represents an Iterator over the SrcSpan elements
pub struct SrcSpanIter {
    /// A reference to the string object corresponding to the SrcSpan
    content: Rc<String>,

    /// The current valid range of the iterator, the next element is given by [range.start]
    range: Range<usize>,
}

/// Implementation of the SrcSpan iterator
impl SrcSpanIter {
    /// Creates a new SrcSpan iterator
    ///
    /// # Panic
    ///
    /// The function will panic if the supplied range is outside backing content
    pub fn new(content: Rc<String>, range: Range<usize>) -> Self {
        assert!(content.len() < range.end);
        SrcSpanIter { content, range }
    }
}

/// Implementation of the [std::iter::Iterator] trait for SrcSpanIter
impl Iterator for SrcSpanIter {
    /// The type of the element is the same as the SrcSpan element
    type Item = Element;

    /// Advances the iterator and returns the next value.
    ///
    /// Returns [`None`] when iteration is finished.
    fn next(&mut self) -> Option<Self::Item> {
        // range is empty <--> iterator is finished.
        if !self.range.is_empty() {
            // record start and bump start value
            let s = self.range.start;
            self.range.start += 1;
            // construct the element by taking the char
            Some(self.content[s..].chars().next().unwrap())
        } else {
            None
        }
    }
}

/// Represents an Iterator over the SrcSpan indices
pub struct SrcSpanIndices {
    /// A reference to the string object corresponding to the SrcSpan
    content: Rc<String>,

    /// The current valid range of the iterator, the next element is given by [range.start]
    range: Range<usize>,

    /// records the start index of this iterator
    start: usize,
}

/// Implementation of the SrcSpanIndices iterator
impl SrcSpanIndices {
    /// Creates a new SrcSpanIndices iterator
    ///
    /// # Panic
    ///
    /// The function will panic if the supplied range is outside backing content
    pub fn new(content: Rc<String>, range: Range<usize>) -> Self {
        assert!(content.len() < range.end);
        let start = range.start;
        SrcSpanIndices {
            content,
            range,
            start,
        }
    }
}

/// Implementation of the [std::iter::Iterator] trait for SrcSpanIndices
impl Iterator for SrcSpanIndices {
    /// Item type is a tuple of the index and the element at this index
    type Item = (usize, Element);

    /// Advances the iterator and returns the next value.
    ///
    /// Returns [`None`] when iteration is finished.
    fn next(&mut self) -> Option<Self::Item> {
        // range is empty <--> iterator is finished.
        if !self.range.is_empty() {
            // record start and bump start value
            let s = self.range.start;
            self.range.start += 1;
            // construct the index and the element
            Some((s - self.start, self.content[s..].chars().next().unwrap()))
        } else {
            None
        }
    }
}

/// Implements the [nom::InputIter] trait for [SrcSpan]
impl InputIter for SrcSpan {
    /// The current input type is a sequence of that Item type.
    type Item = Element;

    /// An iterator over the input type, producing the item and its position for use with Slice.
    type Iter = SrcSpanIndices;

    /// An iterator over the input type, producing the item
    type IterElem = SrcSpanIter;

    /// Returns the [SrcSpanIndices] iterator over the elements and their byte offsets
    #[inline]
    fn iter_indices(&self) -> Self::Iter {
        SrcSpanIndices::new(self.content.clone(), self.range.clone())
    }

    /// Returns the [SrcSpanIter] iterator over the elements
    #[inline]
    fn iter_elements(&self) -> Self::IterElem {
        SrcSpanIter::new(self.content.clone(), self.range.clone())
    }

    /// Finds the byte position of the element
    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        for (o, c) in self.as_str().char_indices() {
            if predicate(c) {
                return Some(o);
            }
        }
        None
    }

    /// Get the byte offset from the element's position in the stream
    #[inline]
    fn slice_index(&self, count: usize) -> Result<usize, Needed> {
        // in the ASCII string, every char is a byte thus we can just thake
        // count if it falls within the length of the SrcSpan
        if self.input_len() >= count {
            Ok(count)
        } else {
            Err(Needed::Unknown)
        }
    }
}

/// Implementation of the [nom::InputTake] trait for [SrcSpan]
impl InputTake for SrcSpan {
    /// Returns a new [SrcSpan] corresponding to the first `count` elements.
    ///
    /// # Panics
    ///
    /// The function panics if `count` > [self.input_len()].
    #[inline]
    fn take(&self, count: usize) -> Self {
        self.from_self_with_subrange(0..count)
    }

    /// Splits the current SrcSpan at `count` returning two new [SrcSpan] objects.ErrorKind
    ///
    /// # Panics
    ///
    /// The function panics if `count` > [self.input_len()].
    #[inline]
    fn take_split(&self, count: usize) -> (Self, Self) {
        // create the new SrcSpan objects
        let first = self.from_self_with_subrange(0..count);
        let second = self.from_self_with_subrange(count..self.input_len());

        // we sould not lose any data
        debug_assert_eq!(first.input_len() + second.input_len(), self.input_len());

        // suffix goes first
        (second, first)
    }
}

/// Implementation of the [nom::InputTakeAtPosition] trait for [SrcSpan]
impl InputTakeAtPosition for SrcSpan {
    /// The current input type is a sequence of that Item type.
    type Item = Element;

    fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.as_str().find(predicate) {
            Some(i) => Ok(self.take_split(i)),
            None => Err(Err::Incomplete(Needed::new(1))),
        }
    }

    fn split_at_position1<P, E: ParseError<Self>>(
        &self,
        predicate: P,
        e: ErrorKind,
    ) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.as_str().find(predicate) {
            Some(0) => Err(Err::Error(E::from_error_kind(self.clone(), e))),
            Some(i) => Ok(self.take_split(i)),
            None => Err(Err::Incomplete(Needed::new(1))),
        }
    }

    fn split_at_position_complete<P, E: ParseError<Self>>(
        &self,
        predicate: P,
    ) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.as_str().find(predicate) {
            Some(i) => Ok(self.take_split(i)),
            None => Ok(self.take_split(self.input_len())),
        }
    }

    fn split_at_position1_complete<P, E: ParseError<Self>>(
        &self,
        predicate: P,
        e: ErrorKind,
    ) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.as_str().find(predicate) {
            Some(0) => Err(Err::Error(E::from_error_kind(self.clone(), e))),
            Some(i) => Ok(self.take_split(i)),
            None => {
                if self.is_empty() {
                    Err(Err::Error(E::from_error_kind(self.clone(), e)))
                } else {
                    Ok(self.take_split(self.input_len()))
                }
            }
        }
    }
}

/// Implementation of the [nom::Slice] trait ([RangeFull]) for [SrcSpan]
impl Slice<RangeFull> for SrcSpan {
    /// Slices self according to the range argument
    #[inline]
    fn slice(&self, _: RangeFull) -> Self {
        self.clone()
    }
}

/// Implementation of the [nom::Slice] trait ([Range]) for [SrcSpan]
impl Slice<Range<usize>> for SrcSpan {
    /// Slices self according to the range argument
    ///
    /// # Panics
    ///
    /// The function panics if the range is out of bounds
    #[inline]
    fn slice(&self, range: Range<usize>) -> Self {
        self.from_self_with_subrange(range)
    }
}

/// Implementation of the [nom::Slice] trait ([RangeTo]) for [SrcSpan]
impl Slice<RangeTo<usize>> for SrcSpan {
    /// Slices self according to the range argument
    ///
    /// # Panics
    ///
    /// The function panics if the range is out of bounds
    #[inline]
    fn slice(&self, range: RangeTo<usize>) -> Self {
        self.slice(0..range.end)
    }
}

/// Implementation of the [nom::Slice] trait ([RangeFrom]) for [SrcSpan]
impl Slice<RangeFrom<usize>> for SrcSpan {
    /// Slices self according to the range argument
    ///
    /// # Panics
    ///
    /// The function panics if the range is out of bounds
    #[inline]
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        self.slice(range.start..self.input_len())
    }
}

/// Implementation of the [nom::Compare] trait for [SrcSpan]
impl Compare<&str> for SrcSpan {
    /// Compares self to another value for equality
    fn compare(&self, t: &str) -> CompareResult {
        self.as_str().compare(t)
    }

    /// Compares self to another value for equality independently of the case.
    fn compare_no_case(&self, t: &str) -> CompareResult {
        self.as_str().compare_no_case(t)
    }
}

/// Implementation of the [nom::FindSubstring] trait for [SrcSpan]
impl FindSubstring<&str> for SrcSpan {
    /// Returns the byte position of the substring if it is found
    fn find_substring(&self, substr: &str) -> Option<usize> {
        self.as_str().find(substr)
    }
}

/// Implementation of the [nom::Offset] trait for [SrcSpan]
impl Offset for SrcSpan {
    /// Offset between the first byte of self and the first byte of the argument
    fn offset(&self, second: &Self) -> usize {
        second.range.start - self.range.start
    }
}

/// Implementation of the [std::fmt::Display] trait for [SrcSpan]
impl fmt::Display for SrcSpan {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let line = self.as_str().lines().next().unwrap_or("");
        write!(f, "{}  {}", self.loc, line)
    }
}

/// implementation of [std::cmp::PartialOrd] for [SrcSpan]
impl PartialOrd for SrcSpan {
    /// This method returns an ordering between self and other values if one exists.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let c = self.loc.context().cmp(&other.loc().context());
        if c != Ordering::Equal {
            return Some(c);
        }

        match self.loc.line().cmp(&other.loc.line()) {
            Ordering::Equal => Some(self.loc.column().cmp(&other.loc.column())),
            o => Some(o),
        }
    }
}

impl From<String> for SrcSpan {
    fn from(span: String) -> Self {
        SrcSpan::new(span)
    }
}

impl From<&str> for SrcSpan {
    fn from(span: &str) -> Self {
        SrcSpan::new(span.to_string())
    }
}

impl Default for SrcSpan {
    fn default() -> Self {
        SrcSpan::empty()
    }
}

#[test]
fn sourcepos_tests() {
    let content = "foo\nbar\nfoobar";
    let sp0 = SrcSpan::new(content.to_string());
    assert_eq!(sp0.slice(4..).as_str(), &content[4..]);
    assert_eq!(sp0.slice(..4).as_str(), &content[..4]);
    assert_eq!(sp0.slice(..4).as_str(), "foo\n");
}

#[test]
fn source_span_test_next() {
    let content = "foo\nbar\nfoobar";
    let mut sp = SrcSpan::new(content.to_string());

    assert_eq!(sp.pos(), (1, 1));

    sp.pos_next();
    assert_eq!(sp.as_str(), &content[1..]);
    assert_eq!(sp.pos(), (1, 2));

    sp.pos_next();
    assert_eq!(sp.as_str(), &content[2..]);
    assert_eq!(sp.pos(), (1, 3));

    sp.pos_next();
    assert_eq!(sp.as_str(), &content[3..]);
    assert_eq!(sp.pos(), (1, 4));

    sp.pos_next();
    assert_eq!(sp.as_str(), &content[4..]);
    assert_eq!(sp.pos(), (2, 1));

    sp.pos_next();
    assert_eq!(sp.as_str(), &content[5..]);
    assert_eq!(sp.pos(), (2, 2));

    sp.pos_prev();
    assert_eq!(sp.as_str(), &content[4..]);
    assert_eq!(sp.pos(), (2, 1));

    sp.pos_prev();
    assert_eq!(sp.as_str(), &content[3..]);
    assert_eq!(sp.pos(), (1, 4));

    sp.pos_prev();
    assert_eq!(sp.as_str(), &content[2..]);
    assert_eq!(sp.pos(), (1, 3));

    sp.pos_prev();
    assert_eq!(sp.as_str(), &content[1..]);
    assert_eq!(sp.pos(), (1, 2));

    sp.pos_prev();
    assert_eq!(sp.as_str(), &content[0..]);
    assert_eq!(sp.pos(), (1, 1));

    sp.pos_prev();
    assert_eq!(sp.as_str(), &content[..]);
    assert_eq!(sp.pos(), (1, 1));
}
