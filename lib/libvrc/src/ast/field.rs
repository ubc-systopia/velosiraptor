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

//! Field Ast Node
//!
//! A field names a part of a state. Either specifically as a (base, offset)
//! from a region, or abstractly within the state.

// used standard library functionality
use std::cmp::min;
use std::fmt::{Debug, Display, Formatter, Result};

// used library internal functionality
use crate::ast::{utils, AstNode, BitSlice, Issues};
use crate::error::{ErrorLocation, VrsError};
use crate::token::TokenStream;

/// Defines an field in the state
///
/// A field may represent a 8, 16, 32, or 64 bit region in the state with a
/// specific bit layout.
#[derive(PartialEq, Clone)]
pub struct Field {
    /// the name of the field
    pub name: String,
    /// a reference to the state where the field is (base + offset)
    pub stateref: Option<(String, u64)>,
    /// the size of the field in bits
    pub length: u64,
    /// a vector of [BitSlice] representing the bitlayout
    pub layout: Vec<BitSlice>,
    /// the position where this field was defined
    pub pos: TokenStream,
}

/// Implementation of the [Display] trait for [Field]
impl Display for Field {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match &self.stateref {
            Some((s, o)) => writeln!(f, "{} [{}, {}, {}] {{", self.name, s, o, self.length)?,
            None => writeln!(f, "{} [{}] {{", self.name, self.length)?,
        };

        self.layout.iter().fold(Ok(()), |result, field| {
            result.and_then(|_| writeln!(f, "  {}", field))
        })?;
        writeln!(f, "}}")
    }
}

/// Implementation of the [Debug] trait for [Field]
impl Debug for Field {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let line = self.pos.line();
        let column = self.pos.column();
        write!(f, "{:03}:{:03} | ", line, column)?;
        match &self.stateref {
            Some((s, o)) => writeln!(f, "{} [{}, {}, {}] {{", self.name, s, o, self.length)?,
            None => writeln!(f, "{} [{}] {{", self.name, self.length)?,
        };

        self.layout.iter().fold(Ok(()), |result, field| {
            result.and_then(|_| writeln!(f, "  {:?}", field))
        })?;
        writeln!(f, "}}")
    }
}

/// implementation of [AstNode] for [Field]
impl AstNode for Field {
    fn check(&self) -> Issues {
        let mut res = Issues::ok();

        // check the length
        let lenoffset = if self.stateref.is_none() { 2 } else { 6 };
        if !([1, 2, 4, 8].contains(&self.length)) {
            let msg = format!("unusual field length: {} bytes", self.length);
            let hint = String::from("change this to either 1, 2, 4, or 8 bytes");
            VrsError::new_err(
                self.pos.from_self(lenoffset..lenoffset + 1),
                msg,
                Some(hint),
            )
            .print();
            res.inc_err(1);
        }

        // check the bitslices in the field
        for b in &self.layout {
            res = res + b.check();
        }

        // check the size of bits
        let maxbits = self.length * 8;
        for b in &self.layout {
            if b.end as u64 >= maxbits {
                let msg = String::from("the bitslice exceeds the size of the field");
                let hint = format!("maximum number of bits is [0..{}]", maxbits - 1);
                VrsError::new_err(b.pos.from_self(0..3), msg, Some(hint)).print();
                res.inc_err(1);
            }
        }

        // check if we have any double entries here:
        let errors = utils::check_double_entries(&self.layout);
        res.inc_err(errors);

        // a vector keeping track of overlap
        let mut overlap: Vec<Option<&BitSlice>> = vec![None; maxbits as usize];
        for b in &self.layout {
            if b.start >= maxbits || b.end > maxbits {
                continue;
            }
            let start = min(b.start, maxbits - 1) as usize;
            let end = min(b.end, maxbits - 1) as usize;
            // run from start up to including end
            for (i, item) in overlap.iter_mut().enumerate().take(end + 1).skip(start) {
                match item {
                    Some(other) => {
                        VrsError::new_overlap(i as u64, b.loc(), other.loc()).print();
                        res.inc_err(errors);
                    }
                    None => {
                        *item = Some(b);
                    }
                }
            }
        }

        // check the name is something like `foo_bar`
        let alllower = self
            .name
            .as_bytes()
            .iter()
            .fold(true, |acc, x| acc & !x.is_ascii_uppercase());

        if !alllower {
            let msg = format!("field `{}` should have an lower case name", self.name);
            let hint = format!(
                "convert the identifier to snake case: `{}`",
                self.name.to_ascii_lowercase()
            );
            VrsError::new_warn(self.pos.from_self(0..1), msg, Some(hint)).print();
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
