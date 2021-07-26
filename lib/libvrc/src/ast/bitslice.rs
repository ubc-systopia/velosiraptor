// Velosiraptor ParseTree
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

//! BitSlice Ast Node

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result};

// used library internal functionality
use crate::ast::{AstNode, Issues};
use crate::error::{ErrorLocation, VrsError};
use crate::token::TokenStream;

/// Represents a bitslice of a [Field]
///
/// The field corresponds to the slice `[start..end]` of the [Field]
#[derive(PartialEq, Clone)]
pub struct BitSlice {
    /// the start bit
    pub start: u64,
    /// the end bit
    pub end: u64,
    /// the name of the slice
    pub name: String,
    /// where it was defined
    pub pos: TokenStream,
}

/// Implementation of the [Display] trait for [BitSlice]
impl Display for BitSlice {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "[{:2}..{:2}]  {}", self.start, self.end, &self.name)
    }
}
/// Implementation of the [Debug] trait for [BitSlice]
impl Debug for BitSlice {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let column = self.pos.column();
        let line = self.pos.line();
        write!(
            f,
            "{:03}:{:03} | [{:2}..{:2}]  {}",
            line, column, self.start, self.end, &self.name
        )
    }
}

/// implementation of [AstNode] for [BitSlice]
impl AstNode for BitSlice {
    fn check(&self) -> Issues {
        let mut res = Issues::ok();
        // check start <= end
        if self.start > self.end {
            let msg = String::from("negative interval detected: start bit > end bit");
            let hint = String::from("swap start with end bits");
            VrsError::new_err(self.pos.with_range(0..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        // no more that 64 bits for now!
        if self.end > 63 {
            let msg = String::from("the bitfield slice exceeds 64 bits.");
            let hint = String::from("reduce the end bit here");
            VrsError::new_err(self.pos.with_range(1..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        // check the name is something like `foo_bar`
        let alllower = self
            .name
            .as_bytes()
            .iter()
            .fold(true, |acc, x| acc & !x.is_ascii_uppercase());

        if !alllower {
            let msg = format!("bitslice `{}` should have an lower case name", self.name);
            let hint = format!(
                "convert the identifier to snake case: `{}`",
                self.name.to_ascii_lowercase()
            );
            VrsError::new_warn(self.pos.with_range(2..3), msg, Some(hint)).print();
            res.inc_warn(1);
        }

        res
    }

    fn name(&self) -> &str {
        &self.name
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        &self.pos
    }
}
