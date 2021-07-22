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

//! The SourcePos definition
//!
//! The SourcePos is a structure containing information about the source file / string
//! that has been parsed. It represents a recognized range of the source file, including
//! its meta information such as the position within the source file.
//!
//! The SourcePos structure implements several traits used by Nom so we can simply pass
//! the SourcePos struct as input/outputs.

use std::fmt;
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};
use std::rc::Rc;

use nom::{
    Compare, CompareResult, Err, FindSubstring, IResult, InputIter, InputLength, InputTake,
    InputTakeAtPosition, Needed, Offset, Slice,
};

use crate::error::ErrorLocation;
use nom::error::{ErrorKind, ParseError};

/// Corresponds to a single byte of the source file
pub type Element = char;

/// The SourcePos tracks the position and content of the string to be lexed
///
/// This structures keeps track of the context (e.g., file name) as well as the
/// current range of the SourcePos within the lexing context as a range of bytes.
/// Moreover, we keep track on the line and column.
#[derive(PartialEq, Clone)]
pub struct SourcePos {
    /// The context of the SourcePos. This might be a file name or "STDIO"
    context: Rc<String>,

    /// Holds a reference counted String objects holding the entire content
    content: Rc<String>,

    /// Holds the valid range within the `content` string
    range: Range<usize>,

    /// The current line of this SourcePos relative to the context. Starting from 1.
    line: u32,

    /// The current column within the current line. Starting from 1.
    column: u32,
}

/// The SourcePos implemetation
impl SourcePos {
    /// Constructor of a new SourcePos with a given input and context.
    ///
    /// It will create new, reference-counted String objects for the context and
    /// the content.
    ///
    /// The meta data of the SourcePos is initialized with the default values:
    ///  - it will start at line 1, column 1
    ///  - the range will cover the entire content
    ///
    /// # Panics
    ///
    /// Panics if the supplied string is non-ascii.
    pub fn new(context: &str, content: &str) -> Self {
        Self::new_at(context, content, 0..content.len(), 1, 1)
    }

    /// Constructor of a new SourcePos with a given input, context, and position.
    ///
    /// It will create new, reference-counted String objects for the context and
    /// the content.
    ///
    /// The meta data of the SourcePos is initialized based on the supplied values.
    /// The range must be valid (i.e., start < end and fall within the content)
    ///
    /// # Panics
    ///
    /// Panics if the supplied string is non-ascii.
    pub fn new_at(
        context: &str,
        content: &str,
        range: Range<usize>,
        line: u32,
        column: u32,
    ) -> Self {
        assert!(range.end <= content.len() && range.start <= range.end);
        assert!(content.is_ascii());
        SourcePos {
            context: Rc::new(context.to_string()),
            content: Rc::new(content.to_string()),
            range,
            line,
            column,
        }
    }

    /// Constructs a new SourcePos from the supplied, reference counted String object
    ///
    /// This function doesn't create new copies of the supplied strings.
    ///
    /// The meta data of the SourcePos is initialized with the default values:
    ///  - it will start at line 1, column 1
    ///  - the range will cover the entire content
    ///
    /// # Panics
    ///
    /// Panics if the supplied string is non-ascii.///
    pub fn from_string(context: Rc<String>, content: Rc<String>) -> Self {
        let len = content.len();
        SourcePos::from_string_at(context, content, 0..len, 1, 1)
    }

    /// Constructor of a new SourcePos from the supplied, reference counted String at position.
    ///
    /// It will create new, reference-counted String objects for the context and
    /// the content.
    ///
    /// The meta data of the SourcePos is initialized based on the supplied values.
    /// The range must be valid (i.e., start < end and fall within the content)
    ///
    /// # Panics
    ///
    /// Panics if the supplied string is non-ascii.
    ///
    pub fn from_string_at(
        context: Rc<String>,
        content: Rc<String>,
        range: Range<usize>,
        line: u32,
        column: u32,
    ) -> Self {
        assert!(range.start <= range.end);
        assert!(range.end <= content.len());
        assert!(content.is_ascii());
        SourcePos {
            context,
            content,
            range,
            line,
            column,
        }
    }

    /// Constructs a new SourcePos covering a subrange of [self]
    ///
    /// This will construct a new SourcePos object with updated range, columns and lines,
    /// but with the same context and content.
    ///
    /// # Panics
    ///
    /// Panics if the supplied range is outside of the covered range by the SourcePos
    pub fn from_self(&self, range: Range<usize>) -> Self {
        assert!(self.input_len() >= range.end - range.start);
        assert!(self.range.start + range.end <= self.range.end);

        // the prefix range are the elements that are skipped
        let prefix = self.range.start..self.range.start + range.start;

        // the new range is the supplied range, shifted by the current range
        let range = self.range.start + range.start..self.range.start + range.end;

        // process characters in prefix, update line and columns accordingly
        let mut line = self.line;
        let mut column = self.column;
        for c in self.content[prefix].chars() {
            // it's either \n or \r\n
            if c as char == '\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
        }

        // finally construct new SourcePos object
        Self::from_string_at(
            self.context.clone(),
            self.content.clone(),
            range,
            line,
            column,
        )
    }

    /// Builds a SourcPos by taking two source positions and forming the span.InputLength
    ///
    /// The new source position will have the same starting position as self.
    /// but with an increased length up to but not including the other one.
    ///
    /// # Panics
    ///
    /// If the two source positions are not related
    pub fn from_self_until(&self, other: &Self) -> Self {
        assert!(self.context == other.context);
        assert!(self.content == other.content);
        assert!(self.range.start <= other.range.start);
        let start = self.range.start;
        let end = other.range.start;
        Self::from_string_at(
            self.context.clone(),
            self.content.clone(),
            start..end,
            self.line,
            self.column,
        )
    }

    /// Creates a new, empty SourcePos object
    ///
    /// This is equivalent to `SourcePos::new("stdio", "")`
    pub fn empty() -> Self {
        Self::new("stdio", "")
    }

    /// Returns true if this SourcePos is empty.
    ///
    /// This is the case when the SourcePos covers the empty range.
    pub fn is_empty(&self) -> bool {
        self.range.is_empty()
    }

    /// Obtains the contents fo the current SourcePos as a `& str`
    ///
    /// This will return a slice into the content given by the current range.
    pub fn as_str(&self) -> &str {
        &self.content[self.range.clone()]
    }

    /// Obtains the current position of this SourcePos in the content
    ///
    /// This returns a (line, column)-tuple.
    pub fn input_pos(&self) -> (u32, u32) {
        (self.line, self.column)
    }

    /// Returns the current range within the content for this SourcePos.
    ///
    /// The range defines the current slice of the input content this SourcePos represents.
    pub fn input_range(&self) -> Range<usize> {
        self.range.clone()
    }

    /// Returns a string reference corresponding to the full input content of this SourcePos.
    pub fn input_content(&self) -> &str {
        &self.content
    }

    /// Returns a string reference of the context for this SourcePos.
    pub fn input_context(&self) -> &str {
        &self.context
    }
}

/// Implements the [nom::InputLength] trait for [SourcePos]
impl InputLength for SourcePos {
    /// Calculates the input length, as indicated by its name, and the name of the trait itself
    fn input_len(&self) -> usize {
        self.range.end - self.range.start
    }
}

/// Represents an Iterator over the SourcePos elements
pub struct SourcePosIter {
    /// A reference to the string object corresponding to the SourcePos
    content: Rc<String>,

    /// The current valid range of the iterator, the next element is given by [range.start]
    range: Range<usize>,
}

/// Implementation of the SourcePos iterator
impl SourcePosIter {
    /// Creates a new SourcePos iterator
    ///
    /// # Panic
    ///
    /// The function will panic if the supplied range is outside backing content
    pub fn new(content: Rc<String>, range: Range<usize>) -> Self {
        assert!(content.len() < range.end);
        SourcePosIter { content, range }
    }
}

/// Implementation of the [std::iter::Iterator] trait for SourcePosIter
impl Iterator for SourcePosIter {
    /// The type of the element is the same as the SourcePos element
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

/// Represents an Iterator over the SourcePos indices
pub struct SourcePosIndices {
    /// A reference to the string object corresponding to the SourcePos
    content: Rc<String>,

    /// The current valid range of the iterator, the next element is given by [range.start]
    range: Range<usize>,

    /// records the start index of this iterator
    start: usize,
}

/// Implementation of the SourcePosIndices iterator
impl SourcePosIndices {
    /// Creates a new SourcePosIndices iterator
    ///
    /// # Panic
    ///
    /// The function will panic if the supplied range is outside backing content
    pub fn new(content: Rc<String>, range: Range<usize>) -> Self {
        assert!(content.len() < range.end);
        let start = range.start;
        SourcePosIndices {
            content,
            range,
            start,
        }
    }
}

/// Implementation of the [std::iter::Iterator] trait for SourcePosIndices
impl Iterator for SourcePosIndices {
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

/// Implements the [nom::InputIter] trait for [SourcePos]
impl InputIter for SourcePos {
    /// The current input type is a sequence of that Item type.
    type Item = Element;

    /// An iterator over the input type, producing the item and its position for use with Slice.
    type Iter = SourcePosIndices;

    /// An iterator over the input type, producing the item
    type IterElem = SourcePosIter;

    /// Returns the [SourcePosIndices] iterator over the elements and their byte offsets
    #[inline]
    fn iter_indices(&self) -> Self::Iter {
        SourcePosIndices::new(self.content.clone(), self.range.clone())
    }

    /// Returns the [SourcePosIter] iterator over the elements
    #[inline]
    fn iter_elements(&self) -> Self::IterElem {
        SourcePosIter::new(self.content.clone(), self.range.clone())
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
        // count if it falls within the length of the SourcePos
        if self.input_len() >= count {
            Ok(count)
        } else {
            Err(Needed::Unknown)
        }
    }
}

/// Implementation of the [nom::InputTake] trait for [SourcePos]
impl<'a> InputTake for SourcePos {
    /// Returns a new [SourcePos] corresponding to the first `count` elements.
    ///
    /// # Panics
    ///
    /// The function panics if `count` > [self.input_len].
    #[inline]
    fn take(&self, count: usize) -> Self {
        assert!(count <= self.input_len());
        self.from_self(0..count)
    }

    /// Splits the current SourcePos at `count` returning two new [SourcePos] objects.ErrorKind
    ///
    /// # Panics
    ///
    /// The function panics if `count` > [self.input_len].
    #[inline]
    fn take_split(&self, count: usize) -> (Self, Self) {
        assert!(count <= self.input_len());
        // create the new SourcePos objects
        let first = self.from_self(0..count);
        let second = self.from_self(count..self.input_len());

        // we sould not lose any data
        assert_eq!(first.input_len() + second.input_len(), self.input_len());

        // suffix goes first
        (second, first)
    }
}

/// Implementation of the [nom::InputTakeAtPosition] trait for [SourcePos]
impl InputTakeAtPosition for SourcePos {
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

/// Implementation of the [nom::Slice] trait ([RangeFull]) for [SourcePos]
impl<'a> Slice<RangeFull> for SourcePos {
    /// Slices self according to the range argument
    #[inline]
    fn slice(&self, _: RangeFull) -> Self {
        // the full range, just return self here
        self.clone()
    }
}

/// Implementation of the [nom::Slice] trait ([Range]) for [SourcePos]
impl<'a> Slice<Range<usize>> for SourcePos {
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

/// Implementation of the [nom::Slice] trait ([RangeTo]) for [SourcePos]
impl<'a> Slice<RangeTo<usize>> for SourcePos {
    /// Slices self according to the range argument
    ///
    /// # Panics
    ///
    /// The function panics if the supplied end range exceeds the current
    /// input length of SourcePos.
    #[inline]
    fn slice(&self, range: RangeTo<usize>) -> Self {
        self.slice(0..range.end)
    }
}

/// Implementation of the [nom::Slice] trait ([RangeFrom]) for [SourcePos]
impl<'a> Slice<RangeFrom<usize>> for SourcePos {
    /// Slices self according to the range argument
    ///
    /// # Panics
    ///
    /// The function panics if the supplied end range exceeds the current
    /// input length of SourcePos.
    #[inline]
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        self.slice(range.start..self.input_len())
    }
}

/// Implementation of the [nom::Compare] trait for [SourcePos]
impl Compare<&str> for SourcePos {
    /// Compares self to another value for equality
    fn compare(&self, t: &str) -> CompareResult {
        let s: &str = self.as_str();
        s.compare(t)
    }

    /// Compares self to another value for equality independently of the case.
    fn compare_no_case(&self, t: &str) -> CompareResult {
        let s: &str = self.as_str();
        s.compare_no_case(t)
    }
}

/// Implementation of the [nom::FindSubstring] trait for [SourcePos]
impl FindSubstring<&str> for SourcePos {
    /// Returns the byte position of the substring if it is found
    fn find_substring(&self, substr: &str) -> Option<usize> {
        self.as_str().find(substr)
    }
}

/// Implementation of the [nom::Offset] trait for [SourcePos]
impl Offset for SourcePos {
    /// Offset between the first byte of self and the first byte of the argument
    fn offset(&self, second: &Self) -> usize {
        let r1 = self.input_range();
        let r2 = second.input_range();

        r2.start - r1.start
    }
}

/// Implementation of the [std::fmt::Display] trait for [SourcePos]
impl fmt::Display for SourcePos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}:{}", self.context, self.line, self.column)
    }
}

/// Implementation of the [std::fmt::Debug] trait for [SourcePos]
impl fmt::Debug for SourcePos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}:{}:{}\n{}",
            self.context,
            self.line,
            self.column,
            self.as_str().to_string()
        )
    }
}

/// Implementation of the [error::ErrorLocation] trait for [SourcePos]
impl ErrorLocation for SourcePos {
    /// the line number in the source file
    fn line(&self) -> u32 {
        self.line
    }

    /// the column number in the source file
    fn column(&self) -> u32 {
        self.column
    }

    /// the length of the token
    fn length(&self) -> usize {
        self.input_len()
    }

    /// the context (stdin or filename)
    fn context(&self) -> &str {
        &self.context
    }

    /// the surrounding line context
    fn linecontext(&self) -> &str {
        let mut start = self.range.start;

        // panic!("start = {}", start);

        for c in self.content[0..start].chars().rev() {
            if c as char == '\n' {
                break;
            }
            start = start - 1;
        }

        if self.content[start..].chars().next().unwrap() == '\n' {
            start = start + 1;
        }

        let mut end = self.range.start;
        for c in self.content[end..].chars() {
            if c as char == '\n' {
                break;
            }
            end = end + 1;
        }
        &self.content[start..end]
    }
}

/// Implementation of the [error::ErrorLocation] trait for [SourcePos]
impl ErrorLocation for &SourcePos {
    /// the line number in the source file
    fn line(&self) -> u32 {
        self.line
    }

    /// the column number in the source file
    fn column(&self) -> u32 {
        self.column
    }

    /// the length of the token
    fn length(&self) -> usize {
        self.input_len()
    }

    /// the context (stdin or filename)
    fn context(&self) -> &str {
        &self.context
    }

    /// the surrounding line context
    fn linecontext(&self) -> &str {
        let mut start = self.range.start;

        // panic!("start = {}", start);

        for c in self.content[0..start].chars().rev() {
            if c as char == '\n' {
                break;
            }
            start = start - 1;
        }

        if self.content[start..].chars().next().unwrap() == '\n' {
            start = start + 1;
        }

        let mut end = self.range.start;
        for c in self.content[end..].chars() {
            if c as char == '\n' {
                break;
            }
            end = end + 1;
        }
        &self.content[start..end]
    }
}

#[test]
fn sourcepos_tests() {
    let content = "foo\nbar\nfoobar";
    let sp0 = SourcePos::new("stdin", content);
    let sp1 = SourcePos::new_at("stdin", content, 4..content.len(), 2, 1);
    assert_eq!(sp0.slice(4..), sp1);
    assert_eq!(sp0.slice(4..).as_str(), &content[4..]);
    assert_eq!(sp0.slice(..4).as_str(), &content[..4]);

    //
    let sp2 = SourcePos::new_at("stdin", content, 0..content.len(), 1, 1);
    assert_eq!(sp0.slice(..4).as_str(), "foo\n");
}
