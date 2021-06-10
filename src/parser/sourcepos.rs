// Velosiraptor Compiler
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

// for reading the file
//use std::fs;

use std::iter::{Copied, Enumerate};
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};
use std::slice::Iter;

use nom::{
    Compare, CompareResult, Err, FindSubstring, IResult, InputIter, InputLength, InputTake,
    InputTakeAtPosition, Needed, Slice,
};

use log::warn;
use nom::error::{ErrorKind, ParseError};

use memchr;

/// Corresponds to a single byte of the source file
pub type Element = u8;

/// The source file type, as an array of bytes.
pub type Content<'a> = &'a [Element];

/// SourcePos structure as input/output to parser combinators
#[derive(Debug, PartialEq, Copy, Clone)]
pub struct SourcePos<'a> {
    /// The name of the file where the content of the source position comes from
    /// or "STDIO" if it was supplied without a file.
    pub filename: &'a str,

    /// Holds the actual content of the that was parsed at this source position
    content: Content<'a>,

    /// The byte offset from the start of the file or supplied input string.
    pub offset: usize,

    /// Line offset into the file or supplied input string, starting from 1.
    pub line: u32,

    /// Column number into the starting line. First column is 1.
    pub column: u32,
}

impl<'a> SourcePos<'a> {
    /// Constructor of a new SourcePos with a given input and filename.
    /// The meta data of the SourcePos is initialized with the default values
    /// for the `offset`, `line`, and `column`
    pub fn new(filename: &'a str, content: Content<'a>) -> Self {
        Self::new_at(filename, content, 0, 1, 1)
    }

    /// Constructs a new SourcePos from the supplied string
    pub fn from_string(filename: &'a str, content: &'a String) -> Self {
        SourcePos::new(filename, content.as_bytes())
    }

    /// Constructor for a new SourcePos at a given position
    pub fn new_at(
        filename: &'a str,
        content: Content<'a>,
        offset: usize,
        line: u32,
        column: u32,
    ) -> Self {
        SourcePos {
            filename: filename,
            offset: offset,
            line: line,
            column: column,
            content: content,
        }
    }

    /// Constructs a new SourcePos from the supplied string
    pub fn from_string_at(
        filename: &'a str,
        content: &'a String,
        offset: usize,
        line: u32,
        column: u32,
    ) -> Self {
        Self::new_at(filename, content.as_bytes(), offset, line, column)
    }

    /// Create a new, empty SourcePos
    pub fn empty() -> Self {
        Self::new("STDIO", b"")
    }

    pub fn is_empty(&self) -> bool {
        return self.content.is_empty();
    }

    /// Obtain the full content of the SourcePos as a slice
    pub fn as_slice(&self) -> Content<'a> {
        self.content
    }
}

/// `Nom::InputLength` implementation for SourcePos (Nom-parser compat)
impl<'a> InputLength for SourcePos<'a> {
    /// Calculates the input length, as indicated by its name, and the name of the trait itself
    fn input_len(&self) -> usize {
        self.content.len()
    }
}

/// `Nomt::InputIter` implementation for SourcePos (Nom-parser compat)
impl<'a> InputIter for SourcePos<'a> {
    /// The current input type is a sequence of that Item type.
    type Item = Element;

    /// An iterator over the input type, producing the item and its position for use with Slice.
    type Iter = Enumerate<Self::IterElem>;

    /// An iterator over the input type, producing the item
    type IterElem = Copied<Iter<'a, Element>>;

    /// Returns an iterator over the elements and their byte offsets
    #[inline]
    fn iter_indices(&self) -> Self::Iter {
        self.content.iter_elements().enumerate()
    }

    /// Returns an iterator over the elements
    #[inline]
    fn iter_elements(&self) -> Self::IterElem {
        self.content.iter().copied()
    }

    /// Finds the byte position of the element
    #[inline]
    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.content.iter().position(|b| predicate(*b))
    }

    /// Get the byte offset from the element's position in the stream
    #[inline]
    fn slice_index(&self, count: usize) -> Result<usize, Needed> {
        if self.content.len() >= count {
            Ok(count)
        } else {
            Err(Needed::new(count - self.content.len()))
        }
    }
}

fn update_line_column(content: Content, line: u32, column: u32) -> (u32, u32) {
    let mut new_line = line;
    let mut new_column = column;
    for c in content {
        if *c as char == '\n' {
            new_line += 1;
            new_column = 1;
        } else {
            new_column += 1;
        }
    }

    (new_line, new_column)
}

/// `Nomt::InputTake` implementation for SourcePos (Nom-parser compat)
impl<'a> InputTake for SourcePos<'a> {
    /// Returns a slice of `count` bytes. panics if count > length
    #[inline]
    fn take(&self, count: usize) -> Self {
        Self::new_at(
            self.filename,
            &self.content[0..count],
            self.offset,
            self.line,
            self.column,
        )
    }

    /// Split the stream at the `count` byte offset. panics if count > length
    #[inline]
    fn take_split(&self, count: usize) -> (Self, Self) {
        let (prefix, suffix) = self.content.split_at(count);
        let p = Self::new_at(self.filename, prefix, self.offset, self.line, self.column);

        let (line, column) = update_line_column(prefix, self.line, self.column);

        let s = Self::new_at(
            self.filename,
            suffix,
            self.offset + prefix.len(),
            line,
            column,
        );
        // suffix goes first
        (s, p)
    }
}

/// `Nomt::InputTakeAtPosition` implementation for SourcePos (Nom-parser compat)
impl<'a> InputTakeAtPosition for SourcePos<'a> {
    /// The current input type is a sequence of that Item type.
    type Item = Element;

    fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match (0..self.content.len()).find(|b| predicate(self.content[*b])) {
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
        match (0..self.content.len()).find(|b| predicate(self.content[*b])) {
            Some(0) => Err(Err::Error(E::from_error_kind(*self, e))),
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
        match (0..self.content.len()).find(|b| predicate(self.content[*b])) {
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
        match (0..self.content.len()).find(|b| predicate(self.content[*b])) {
            Some(0) => Err(Err::Error(E::from_error_kind(*self, e))),
            Some(i) => Ok(self.take_split(i)),
            None => {
                if self.is_empty() {
                    Err(Err::Error(E::from_error_kind(*self, e)))
                } else {
                    Ok(self.take_split(self.input_len()))
                }
            }
        }
    }
}

/// `Nomt::InputTakeAtPosition` implementation for SourcePos (Nom-parser compat)
impl<'a> Slice<RangeFull> for SourcePos<'a> {
    fn slice(&self, _: RangeFull) -> Self {
        // the full range, just return self here
        *self
    }
}

impl<'a> Slice<Range<usize>> for SourcePos<'a> {
    fn slice(&self, range: Range<usize>) -> Self {
        // get the new range
        let start = range.start;
        let new_content = &self.content[range];

        // no change in content, just return self
        if new_content == self.content {
            return *self;
        }

        // the start is 0, so we can just return the new span with the same offsets etc
        if start == 0 {
            return Self::new_at(
                self.filename,
                new_content,
                self.offset,
                self.line,
                self.column,
            );
        }

        // workout the new column and content index
        let (line, column) = update_line_column(&self.content[..start], self.line, self.column);

        // return the new SourcePos
        Self::new_at(
            self.filename,
            new_content,
            self.offset + start,
            line,
            column,
        )
    }
}

impl<'a> Slice<RangeTo<usize>> for SourcePos<'a> {
    fn slice(&self, range: RangeTo<usize>) -> Self {
        // return the slice from 0..range.end
        self.slice(0..range.end)
    }
}

impl<'a> Slice<RangeFrom<usize>> for SourcePos<'a> {
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        // return the slice from range.start..content.len
        self.slice(range.start..self.content.len())
    }
}

fn lowercase_byte(c: u8) -> u8 {
    match c {
        b'A'..=b'Z' => c - b'A' + b'a',
        _ => c,
    }
}

/// `Nom::Compare` implementation for SourcePos (Nom-parser compat)
impl<'a, 'b> Compare<Content<'b>> for SourcePos<'a> {
    /// Compares self to another value for equality
    fn compare(&self, t: Content<'b>) -> CompareResult {
        let pos = self.content.iter().zip(t.iter()).position(|(a, b)| a != b);

        match pos {
            Some(_) => CompareResult::Error,
            None => {
                if self.content.len() >= t.len() {
                    CompareResult::Ok
                } else {
                    CompareResult::Incomplete
                }
            }
        }
    }

    /// Compares self to another value for equality independently of the case.
    fn compare_no_case(&self, t: Content<'b>) -> CompareResult {
        if self
            .content
            .iter()
            .zip(t)
            .any(|(a, b)| lowercase_byte(*a) != lowercase_byte(*b))
        {
            CompareResult::Error
        } else if self.content.len() < t.len() {
            CompareResult::Incomplete
        } else {
            CompareResult::Ok
        }
    }
}

/// `Nom::FindSubstring` implementation for SourcePos (Nom-parser compat)
impl<'a, 'b> FindSubstring<Content<'b>> for SourcePos<'a> {
    /// Returns the byte position of the substring if it is found
    fn find_substring(&self, substr: &'b [u8]) -> Option<usize> {
        if substr.len() > self.content.len() {
            return None;
        }

        let (&substr_first, substr_rest) = match substr.split_first() {
            Some(split) => split,
            // an empty substring is found at position 0
            // This matches the behavior of str.find("").
            None => return Some(0),
        };

        if substr_rest.is_empty() {
            return memchr::memchr(substr_first, self.content);
        }

        let mut offset = 0;
        let haystack = &self.content[..self.content.len() - substr_rest.len()];

        while let Some(position) = memchr::memchr(substr_first, &haystack[offset..]) {
            offset += position;
            let next_offset = offset + 1;
            if &self.content[next_offset..][..substr_rest.len()] == substr_rest {
                return Some(offset);
            }

            offset = next_offset;
        }

        None
    }
}


#[test]
fn sourcepos_tests() {
    let sp0 = SourcePos::new("stdin", b"foo\nbar\nfoobar");
    let sp1 = SourcePos::new_at("stdin", b"bar\nfoobar", 4, 2, 1);
    assert_eq!(sp0.slice(4..), sp1);
    let sp2 = SourcePos::new_at("stdin", b"foo\n", 0, 1, 1);
    assert_eq!(sp0.slice(..4), sp2);
}
