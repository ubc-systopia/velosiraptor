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

// std library imports
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result};

use crate::ast::{
    utils, AstNode, AstNodeGeneric, Expr, Issues, Symbol, SymbolKind, SymbolTable, Type,
};
use crate::error::{ErrorLocation, VrsError};
use crate::token::TokenStream;

use super::MapEntry;

/// Represents a list comprehension map `map = [Unit(args) @ offset for x in 0..1024]`
#[derive(PartialEq, Clone)]
pub struct ListComprehensionMap {
    /// the entries in the explicit map
    pub entry: MapEntry,

    /// the iterator variable
    pub var: String,

    /// the possible range the variable [var] may take
    pub range: Expr,

    /// the position of the map in the source code
    pub pos: TokenStream,
}

impl ListComprehensionMap {
    pub fn new(entry: MapEntry, var: String, range: Expr, pos: TokenStream) -> Self {
        ListComprehensionMap {
            entry,
            var,
            range,
            pos,
        }
    }

    pub fn set_entry(mut self, entry: MapEntry) -> Self {
        self.entry = entry;
        self
    }

    pub fn set_var(mut self, var: String) -> Self {
        self.var = var;
        self
    }

    pub fn set_range(mut self, range: Expr) -> Self {
        self.range = range;
        self
    }

    pub fn finalize(mut self, pos: &TokenStream) -> Self {
        self.pos = self.pos.expand_until(pos);
        self
    }

    pub fn get_unit_names(&self) -> Vec<String> {
        vec![self.entry.get_unit_name().to_string()]
    }

    pub fn get_range_max(&self) -> u64 {
        match &self.range {
            Expr::Range { end, .. } => {
                if let Expr::Number { value, .. } = end.as_ref() {
                    *value
                } else {
                    panic!("not a fixed number.");
                }
            }
            _ => panic!("unsupported range expression"),
        }
    }
}

/// implementation of the [fmt::Display] trait for the [Segment]
impl Display for ListComprehensionMap {
    fn fmt(&self, f: &mut Formatter) -> Result {
        writeln!(
            f,
            "map = [{} for {} in {}]",
            self.entry, self.var, self.range
        )
    }
}

/// implementation of the [fmt::Debug] trait for the [Segment]
impl Debug for ListComprehensionMap {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let line = self.loc().line();
        let column = self.loc().column();

        writeln!(
            f,
            "{:03}:{:03} | map = [{} for {} in {}]",
            line, column, self.entry, self.var, self.range
        )
    }
}

/// Implementation of [AstNodeGeneric] for [Map]
impl<'a> AstNodeGeneric<'a> for ListComprehensionMap {
    // checks the node and returns the number of errors and warnings encountered
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        // all fine for now
        let mut res = Issues::ok();

        // set the current context
        st.create_context(String::from("listcomprehension"));

        // Check 1: Check the range expression for defined symbols
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that the range expression is well-defined
        // Notes:       We need to do this *before* we add the variable to the symbol table
        // --------------------------------------------------------------------------------------

        let (start, end) = if let Expr::Range { start, end, .. } = &self.range {
            // check the range expression
            res = res + self.range.check(st);

            if !start.is_const_expr(st) {
                let msg = String::from("start of range expression is not constant");
                let hint = String::from("make this expression constant");
                VrsError::new_err(start.loc().clone(), msg, Some(hint)).print();
                res.inc_err(1);
            }

            if !end.is_const_expr(st) {
                let msg = String::from("end of range expression is not constant");
                let hint = String::from("make this expression constant");
                VrsError::new_err(start.loc().clone(), msg, Some(hint)).print();
                res.inc_err(1);
            }

            let novars = HashMap::new();
            let start =
                if let Expr::Number { value, .. } = start.clone().fold_constants(st, &novars) {
                    value
                } else {
                    panic!("constant expression `{}` didn't fold into a number!", start);
                };

            let end = if let Expr::Number { value, .. } = end.clone().fold_constants(st, &novars) {
                value
            } else {
                panic!("constant expression `{}` didn't fold into a number!", end);
            };

            if start == end {
                let msg = String::from("empty range expression with start == end.");
                let hint = String::from("define range with start < end");
                VrsError::new_warn(self.range.loc().clone(), msg, Some(hint)).print();
                res.inc_warn(1);
            }

            if start > end {
                let msg = String::from("start of range is larger than end of range");
                let hint = String::from("define range with start < end");
                VrsError::new_err(self.range.loc().clone(), msg, Some(hint)).print();
                res.inc_err(1);
            }

            (start, end)
        } else {
            let msg = String::from("expression is not a range expression.");
            let hint =
                String::from("convert exprssion into a range expression of format `start..end`");
            VrsError::new_err(self.pos.clone(), msg, Some(hint)).print();
            res.inc_err(1);

            (0, 0) // we just return the zero interval ehre
        };

        // now add the iterator variable to the symbol table

        let varsym = Symbol::new(
            self.var.clone(),
            Type::Integer,
            SymbolKind::Variable,
            self.pos.clone(),
            AstNode::Expression(&self.range),
        );

        // try to insert the variable into the symbol table
        if !st.insert(varsym) {
            res.inc_err(1);
        }

        // Check 2: Check the entry for well-formedness
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that the entry is well-defined
        // Notes:
        // --------------------------------------------------------------------------------------
        res = res + self.entry.check(st);

        // Check 3: Variable name
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: Check if the unit name is snake case.
        // Notes:       --
        // --------------------------------------------------------------------------------------

        res = res + utils::check_snake_case(self.var.as_str(), &self.pos);

        // Check 4: Range over lap
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check if the input address ranges may overlap
        // Notes:       --
        // --------------------------------------------------------------------------------------

        // we only need to do the check if the range is not empty, otherwise it's non-overlapping
        // by construction
        if self.entry.has_range() {
            // collect all ranges
            let mut ranges = Vec::new();
            for i in start..end {
                let range = self.entry.eval_range(&self.var, i, st);
                ranges.push((i, range));
            }

            let ranges_overlap = utils::check_ranges_overlap(&mut ranges);

            for (i, j) in ranges_overlap {
                let msg = format!(
                    "range overlap: input address range of element {} ({:x}..{:x}) overlaps with element {} ({:x}..{:x})",
                    ranges[i].0,
                    ranges[i].1.start,
                    ranges[i].1.end,
                    ranges[j].0,
                    ranges[j].1.start,
                    ranges[j].1.end
                );
                let hint = String::from("change input address range to non-overlapping values");
                VrsError::new_err(self.entry.loc().clone(), msg, Some(hint)).print();
                res.inc_err(1);
            }
        }

        // drop the context again
        st.drop_context();

        res
    }

    /// returns a printable string representation of the ast node
    fn name(&self) -> &str {
        "map"
    }

    /// returns the location of the AstNodeGeneric
    fn loc(&self) -> &TokenStream {
        &self.pos
    }
}
