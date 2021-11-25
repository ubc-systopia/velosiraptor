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
use crate::ast::{utils, AstNodeGeneric, Issues, SymbolTable};
use crate::error::{ErrorLocation, VrsError};
use crate::token::TokenStream;

/// Represents a bitslice of a [Field]
///
/// The field corresponds to the slice `[start, end]` of the [Field]
/// The end bit is including `[start..=end]`
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

impl BitSlice {
    /// constructs the mask value of the bit slice
    ///
    /// # Example
    /// start = 0, end = 3 -> 0xf
    pub fn mask_value(&self) -> u64 {
        let mut mask = 0;
        for i in self.start..=self.end {
            mask |= 1 << i;
        }
        mask
    }

    /// returns the number of bits this slice covers
    pub fn nbits(&self) -> u64 {
        self.end - self.start + 1
    }
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

/// implementation of [AstNodeGeneric] for [BitSlice]
impl AstNodeGeneric for BitSlice {
    /// checks the bitslices node and reports issues
    fn check(&self, _st: &mut SymbolTable) -> Issues {
        let mut res = Issues::ok();

        // Check 1: Valid range.
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: The interval specified by `start` and `end` must be valid, i.e.,
        //              start <= end must hold.
        // Notes:       We test for overlaps in the parent node.
        // --------------------------------------------------------------------------------------

        if self.start > self.end {
            let msg = String::from("negative interval detected: start bit > end bit");
            let hint = String::from("swap start with end bits");
            VrsError::new_err(self.pos.with_range(0..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        // Check 2: Size of bits
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Currently, no more than 64 bits are supported, thus the end bit must be
        //              less or equal to 63.
        // Notes:       We test for the total field size in the parent node.
        // --------------------------------------------------------------------------------------

        if self.end > 63 {
            let msg = String::from("the bitfield slice exceeds 64 bits.");
            let hint = String::from("reduce the end bit here");
            VrsError::new_err(self.pos.with_range(1..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        // Check 3: Identifier is ASCII
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: The name of the bitslice must be in ASCII characters.
        // Notes:       --
        // --------------------------------------------------------------------------------------

        if !self.name.is_ascii() {
            let msg = format!("constant `{}` should be in ASCII", self.name);
            let hint = format!(
                "convert the identifier to ASCII: `{}`",
                self.name.to_ascii_uppercase()
            );
            VrsError::new_err(self.pos.with_range(1..2), msg, Some(hint)).print();
            res.inc_err(1);
        }

        // Check 4: Identifier format
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: The identifier should be in `snake_case`.
        // Notes:       We test for double defined slices in the parent node.
        // --------------------------------------------------------------------------------------

        res + utils::check_snake_case(&self.name, &self.pos)
    }

    fn name(&self) -> &str {
        &self.name
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        &self.pos
    }
}
