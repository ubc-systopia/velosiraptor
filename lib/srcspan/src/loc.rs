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

//! # The SrcLoc Definition
//!
//! Represents a location in a source file, or string

// Standard library imports
use std::fmt::{Display, Formatter, Result};
use std::rc::Rc;

/// Represents the source location
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct SrcLoc {
    /// The context of the SrcSpan. This might be a file name.
    context: Option<Rc<String>>,

    /// The current line of this SrcSpan relative to the context. Starting from 1.
    line: u32,

    /// The current column within the current line. Starting from 1.
    column: u32,
}

impl SrcLoc {
    /// Creates a new SrcLoc
    pub fn new() -> Self {
        Self {
            context: None,
            line: 1,
            column: 1,
        }
    }

    /// Sets the context in the [SrcLoc]
    pub fn set_context(&mut self, context: String) {
        self.context = Some(Rc::new(context));
    }

    /// Obtains the context from the [SrcLoc]
    pub fn context(&self) -> Option<&str> {
        Some(self.context.as_deref()?.as_str())
    }

    /// Obtains the current line of the [SrcLoc]
    pub fn line(&self) -> u32 {
        self.line
    }

    /// Obtains the current column of the [SrcLoc]
    pub fn column(&self) -> u32 {
        self.column
    }

    /// Obtains the location (line, column) of the [SrcLoc]
    pub fn loc(&self) -> (u32, u32) {
        (self.line, self.column)
    }

    /// Sets the location to the beginning of the file
    pub fn start_of_file(&mut self) {
        self.line = 1;
        self.column = 1;
    }

    /// Sets the location to the start of the line
    pub fn start_of_line(&mut self) {
        self.column = 1;
    }

    /// Increases the column number by `n`
    pub fn inc_column(&mut self, n: u32) {
        self.column += n;
    }

    /// Increases the line number by `n`
    pub fn inc_line(&mut self, n: u32) {
        self.line += n;
    }

    /// Decrements the column number by `n`
    pub fn dec_column(&mut self, n: u32) {
        if n > self.column {
            self.column = 1;
        } else {
            self.column -= n;
        }
    }

    /// Decrements the line number by `n`
    pub fn dec_line(&mut self, n: u32) {
        if n > self.line {
            self.line = 1;
        } else {
            self.line -= n;
        }
    }
}

/// Implementation of the [Display] trait for [SrcSpan]
impl Display for SrcLoc {
    fn fmt(&self, f: &mut Formatter) -> Result {
        if let Some(c) = &self.context {
            write!(f, "{}:{}:{}", c, self.line, self.column)
        } else {
            write!(f, "$buf:{}:{}", self.line, self.column)
        }
    }
}

/// Implementation of the [Default] trait for [SrcSpan]
impl Default for SrcLoc {
    fn default() -> Self {
        Self::new()
    }
}
