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
use crate::ast::{utils, AstNodeGeneric, BitSlice, Issues, Symbol, SymbolKind, SymbolTable, Type};
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
    /// the size of the field in bytes
    pub length: u64,
    /// a vector of [BitSlice] representing the bitlayout
    pub layout: Vec<BitSlice>,
    /// the position where this field was defined
    pub pos: TokenStream,
}

impl Field {
    /// constructs the mask value of the bit slices in the field
    pub fn mask_value(&self) -> u64 {
        let mut maskval = 0;
        for s in &self.layout {
            maskval |= s.mask_value();
        }

        maskval
    }

    pub fn nbits(&self) -> u64 {
        self.length * 8
    }

    pub fn location(&self) -> String {
        self.pos.location()
    }

    /// converts the field into a symbol
    pub fn to_symbol(&self) -> Symbol {
        // prepend the 'state' prefix
        let name = format!("state.{}", self.name);
        Symbol::new(name, Type::Integer, SymbolKind::State, self.pos.clone())
    }

    /// builds the symboltable for the state related symbols
    pub fn build_symboltable(&self, st: &mut SymbolTable) {
        // insert the own symbol
        st.insert(self.to_symbol());

        for s in &self.layout {
            let name = format!("state.{}.{}", self.name, s.name);
            st.insert(Symbol::new(
                name,
                Type::Integer,
                SymbolKind::State,
                s.loc().clone(),
            ));
        }
    }
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

/// implementation of [AstNodeGeneric] for [Field]
impl AstNodeGeneric for Field {
    fn check(&self, st: &mut SymbolTable) -> Issues {
        let mut res = Issues::ok();

        // We already know that the bases are valid

        // Check 1: Check all BitSlices
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Errors
        // Description: Check all the BitSlices
        // Notes:       --
        // --------------------------------------------------------------------------------------

        for b in &self.layout {
            res = res + b.check(st);
        }

        // Check 2: Field size
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: The size of the field must be one of 1, 2, 4, 8
        // Notes:       Technically, other values could be allowed
        // --------------------------------------------------------------------------------------

        if !([1, 2, 4, 8].contains(&self.length)) {
            let lenoffset = if self.stateref.is_none() { 2 } else { 6 };
            let msg = format!("unusual field length: {} bytes", self.length);
            let hint = String::from("change this to either 1, 2, 4, or 8 bytes");
            VrsError::new_err(
                self.pos.with_range(lenoffset..lenoffset + 1),
                msg,
                Some(hint),
            )
            .print();
            res.inc_err(1);
        }

        // Check 3: BitSlice sizes
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that all BitSlices are within the size of the field
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let maxbits = self.length * 8;
        for b in &self.layout {
            if b.end as u64 >= maxbits {
                let msg = String::from("the bitslice exceeds the size of the field");
                let hint = format!("maximum number of bits is [0..{}]", maxbits - 1);
                VrsError::new_err(b.pos.with_range(0..3), msg, Some(hint)).print();
                res.inc_err(1);
            }
        }

        // Check 4: Double defined bitslices
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that all BitSlices of this field have distinct names
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let errors = utils::check_double_entries(&self.layout);
        res.inc_err(errors);

        // Check 5: Overlap check
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that the BitSlices do not overlap
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let mut overlap: Vec<Option<&BitSlice>> = vec![None; maxbits as usize];
        for b in &self.layout {
            // skip the ones that overshoot
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

        // Check 6: Identifier snake_case
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: Checks if the identifier has snake_case
        // Notes:       --
        // --------------------------------------------------------------------------------------

        res = res + utils::check_snake_case(&self.name, &self.pos);

        // Check 6: Bases defined
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Checks if the field has well-defined base
        // Notes:       --
        // --------------------------------------------------------------------------------------
        if let Some(sref) = &self.stateref {
            if let Some(sym) = st.lookup(&sref.0) {
                // we found the symbol, check type
                if sym.kind != SymbolKind::Parameter {
                    VrsError::new_double_kind(
                        String::from(&sref.0),
                        self.loc().with_range(1..2),
                        sym.loc.clone(),
                    )
                    .print();
                    res.inc_err(1);
                }
                if sym.typeinfo != Type::Address {
                    VrsError::new_double_type(
                        String::from(&sref.0),
                        self.loc().with_range(1..2),
                        sym.loc.clone(),
                    )
                    .print();
                    res.inc_err(1);
                }
            } else {
                // undefined base
                let msg = format!("field `{}` has invalid state ref `{}`", self.name, sref.0);
                let hint = format!("add a `{} : addr to the state params", sref.0);
                VrsError::new_err(self.loc().with_range(1..2), msg, Some(hint)).print();
            }
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
