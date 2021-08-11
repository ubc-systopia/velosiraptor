// Velosiraptor Ast
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

//! Issue Tracking

// Used standard library functionality
use std::fmt::Display;
use std::ops::Add;

/// struct for counting issues
///
/// Keeps track of the number of encountered errors and warnings
#[derive(Debug, PartialEq)]
pub struct Issues {
    /// the number of encountered errors
    pub errors: u32,
    /// the number of encountered warnings
    pub warnings: u32,
}

/// Implementation
impl Issues {
    /// creates a new issues object with the given errors and warnings
    pub fn new(errors: u32, warnings: u32) -> Self {
        Issues { errors, warnings }
    }

    /// creates a new issues object with no warnings or errors
    pub fn ok() -> Self {
        Self::new(0, 0)
    }

    /// creates a new issues object corresponding to a single warning
    pub fn warn() -> Self {
        Self::new(0, 1)
    }

    /// creates a new issues object corresponding to a single error
    pub fn err() -> Self {
        Self::new(1, 0)
    }

    /// incremennts the error count by the given value
    pub fn inc_err(&mut self, c: u32) {
        self.errors += c;
    }

    /// incremennts the warnings count by the given value
    pub fn inc_warn(&mut self, c: u32) {
        self.warnings += c;
    }

    /// returns true if we have found error issues
    pub fn is_err(&self) -> bool {
        self.errors > 0
    }
}

/// implementation of [Dispaly] for [Issues]
impl Display for Issues {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "errors: {}  warnings: {}", self.errors, self.warnings)
    }
}

/// implementation of [Dispaly] for [Issues]
///
/// Implementation of the addition operator on the Issues object
impl Add for Issues {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self {
            warnings: self.warnings + other.warnings,
            errors: self.errors + other.errors,
        }
    }
}
