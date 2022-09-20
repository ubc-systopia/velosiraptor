// Velosiraptor Parser
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! MAP ast node

// standard library includes
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result};

use crate::ast::{AstNode, AstNodeGeneric, Expr, Issues, SymbolKind, SymbolTable, Type};
use crate::error::VrsError;
use crate::token::TokenStream;

mod explicit;
mod list;

pub use explicit::ExplicitMap;
pub use list::ListComprehensionMap;

/// Defines a mapping between addresses and units
#[derive(PartialEq, Debug, Clone)]
pub enum Map {
    /// explicit map
    Explicit(ExplicitMap),
    /// list comprehension map
    ListComprehension(Box<ListComprehensionMap>),
}

impl Map {
    pub fn get_unit_names(&self) -> Vec<String> {
        match self {
            Map::Explicit(explicit) => explicit.get_unit_names(),
            Map::ListComprehension(list) => list.get_unit_names(),
        }
    }
}

/// Implementation of [AstNodeGeneric] for [Map]
impl<'a> AstNodeGeneric<'a> for Map {
    // checks the node and returns the number of errors and warnings encountered
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        match self {
            Map::Explicit(map) => map.check(st),
            Map::ListComprehension(map) => map.check(st),
        }
    }

    /// rewrite the ast
    fn rewrite(&'a mut self) {
        match self {
            Map::Explicit(map) => map.rewrite(),
            Map::ListComprehension(map) => map.rewrite(),
        };
    }

    /// returns a printable string representation of the ast node
    fn name(&self) -> &str {
        match self {
            Map::Explicit(map) => map.name(),
            Map::ListComprehension(map) => map.name(),
        }
    }

    /// returns the location of the AstNodeGeneric
    fn loc(&self) -> &TokenStream {
        match self {
            Map::Explicit(map) => map.loc(),
            Map::ListComprehension(map) => map.loc(),
        }
    }
}

/// Defines an entry in the [StaticMap] unit
///
/// The canonical form of a map entry is: `INPUT RANGE => Unit(arglist) @ offset`
/// where
///   - INPUT RANGE is optional
///   - arglist may be empty
///   - offset is optional
#[derive(PartialEq, Clone)]
pub struct MapEntry {
    /// range expressiong of the input address range that this entry maps
    pub range: Option<Expr>,
    /// the name of the unit this entry maps to
    pub unit_name: String,
    /// list of expressions to initialize the unit parameters
    pub unit_params: Vec<Expr>,
    /// offset into the unit
    pub offset: Option<Expr>,
    /// the position of the map in the source code
    pub pos: TokenStream,
}

use std::ops::Range;

impl MapEntry {
    pub fn new(pos: TokenStream, unit: String) -> Self {
        Self {
            range: None,
            unit_name: unit,
            unit_params: vec![],
            offset: None,
            pos,
        }
    }

    pub fn set_range(mut self, range: Option<Expr>) -> Self {
        self.range = range;
        self
    }

    pub fn add_unit_param(mut self, param: Expr) -> Self {
        self.unit_params.push(param);
        self
    }

    pub fn add_unit_params(mut self, params: Vec<Expr>) -> Self {
        self.unit_params.extend(params);
        self
    }

    pub fn set_offset(mut self, offset: Option<Expr>) -> Self {
        self.offset = offset;
        self
    }

    pub fn finalize(mut self, pos: &TokenStream) -> Self {
        self.pos = self.pos.expand_until(pos);
        self
    }

    pub fn has_range(&self) -> bool {
        self.range.is_some()
    }

    pub fn eval_range(&self, var: &str, val: u64, st: &mut SymbolTable) -> Range<u64> {
        if let Some(range) = &self.range {
            let mut vars = HashMap::new();
            vars.insert(var.to_string(), val);

            if let Expr::Range { start, end, .. } = range.fold_constants(st, &vars) {
                match (*start, *end) {
                    (Expr::Number { value: s, .. }, Expr::Number { value: e, .. }) => s..e,
                    (s, e) => {
                        panic!("range expressions not numbers: {}..{}", s, e);
                    }
                }
            } else {
                panic!("unexpected expression! {}", range);
            }
        } else {
            println!("warning: no range specified for map entry");
            0..0
        }
    }

    pub fn get_unit_name(&self) -> &str {
        &self.unit_name
    }
}

/// implementation of the [fmt::Display] trait for the [Segment]
impl Display for MapEntry {
    fn fmt(&self, f: &mut Formatter) -> Result {
        if let Some(range) = &self.range {
            write!(f, "{} => ", range)?;
        }

        let params = self
            .unit_params
            .iter()
            .map(|p| p.to_string())
            .collect::<Vec<String>>()
            .join(", ");
        write!(f, " {}({})", self.unit_name, params)?;

        if let Some(offset) = &self.offset {
            write!(f, " @ {}", offset)?;
        }
        Ok(())
    }
}

/// implementation of the [fmt::Debug] trait for the [Segment]
impl Debug for MapEntry {
    fn fmt(&self, f: &mut Formatter) -> Result {
        Display::fmt(self, f)
    }
}

/// Implementation of [AstNodeGeneric] for [Map]
impl<'a> AstNodeGeneric<'a> for MapEntry {
    // checks the node and returns the number of errors and warnings encountered
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        // all fine for now
        let mut res = Issues::ok();

        // Check 1: Check whether the unit parameters are well-formed
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check the expressions of the unit parameteres
        // Notes:
        // --------------------------------------------------------------------------------------

        for p in &self.unit_params {
            res = res + p.check(st);
        }

        // Check 2: See whether the unit has been defined
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that the unit exists
        // Notes:
        // --------------------------------------------------------------------------------------

        let unit = st.lookup_with_kind(&self.unit_name, &[SymbolKind::Unit]);
        if unit.is_none() {
            let msg = format!("reference to unknown unit '{}'", self.unit_name);
            let hint = String::from("define this unit or import unit definition.");
            VrsError::new_err(self.loc().clone(), msg, Some(hint)).print();
            res.inc_err(1);
        }

        // Check 3: Match the unit parameters
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check the unit parameters
        // Notes:
        // --------------------------------------------------------------------------------------

        if let Some(unit) = unit {
            let uparams = match unit.ast_node {
                AstNode::StaticMap(u) => u.params.as_slice(),
                AstNode::Segment(u) => u.params.as_slice(),
                _ => &[],
            };

            for (i, p) in self.unit_params.iter().enumerate() {
                if i >= uparams.len() {
                    let msg = format!("excess parameter for unit '{}'", self.unit_name);
                    let hint = String::from("remove this parameter");
                    VrsError::new_err(self.loc().clone(), msg, Some(hint)).print();
                    res.inc_err(1);
                    continue;
                }
                res = res + p.match_type(uparams[i].ptype, st);
            }
        }

        // Check 3: Validate offset expression
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check the offset expression
        // Notes:
        // --------------------------------------------------------------------------------------

        if let Some(offset) = &self.offset {
            res = res + offset.check(st) + offset.match_type(Type::Integer, st);
        }

        // Check 4: Check the range expression
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Validates the range expression
        // Notes:
        // --------------------------------------------------------------------------------------

        if let Some(range) = &self.range {
            res = res + range.check(st);
            if let Expr::Range { .. } = range {
            } else {
                let msg = format!("range expression expected, found: {}", range);
                let hint = String::from("convert this to a range expression: `start..end`");
                VrsError::new_err(self.loc().clone(), msg, Some(hint)).print();
                res.inc_err(1)
            }
        }

        res
    }

    /// returns a printable string representation of the ast node
    fn name(&self) -> &str {
        "mapentry"
    }

    /// returns the location of the AstNodeGeneric
    fn loc(&self) -> &TokenStream {
        &self.pos
    }
}
