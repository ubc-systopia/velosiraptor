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

//! Utils library

use crate::ast::{AstNodeGeneric, Issues};
use crate::error::VrsError;
use crate::token::TokenStream;
use std::collections::HashMap;

/// drains the list and merges it into the hashmap
pub fn collect_list<'a, T: AstNodeGeneric<'a>>(
    list: &mut Vec<T>,
    hmap: &mut HashMap<String, T>,
) -> u32 {
    let mut errors = 0;
    for elm in list.drain(..) {
        let key = elm.name();
        match hmap.get(key) {
            Some(prev) => {
                errors += 1;
                VrsError::new_double(
                    key.to_string(),
                    elm.loc().with_range(0..2),
                    prev.loc().with_range(0..2),
                )
                .print();
            }
            None => {
                // insert the elemement into the hashmap
                hmap.insert(String::from(key), elm);
            }
        }
    }
    // return the errors
    errors
}

/// drains the list and merges it into the hashmap
pub fn check_double_entries<'a, T: AstNodeGeneric<'a>>(nodelist: &[T]) -> u32 {
    let mut errors = 0;
    let mut hmap = HashMap::new();

    for (idx, elm) in nodelist.iter().enumerate() {
        let key = elm.name();
        match hmap.get(key) {
            Some(previdx) => {
                errors += 1;
                let prev: &T = nodelist.get(*previdx).unwrap();
                VrsError::new_double(
                    key.to_string(),
                    elm.loc().with_range(0..2),
                    prev.loc().with_range(0..2),
                )
                .print();
            }
            None => {
                // insert the elemement into the hashmap
                hmap.insert(String::from(key), idx);
            }
        }
    }
    // return the errors
    errors
}

/// checks if the identifier has snake case
pub fn check_snake_case(name: &str, loc: &TokenStream) -> Issues {
    // check the name is something like `foo_bar`
    let alllower = name
        .as_bytes()
        .iter()
        .fold(true, |acc, x| acc & !x.is_ascii_uppercase());

    if !alllower {
        let msg = format!("identifier `{}` should have an lower case name", name);
        let hint = format!(
            "convert the identifier to snake case: `{}`",
            name.to_ascii_lowercase()
        );
        VrsError::new_warn(loc.with_range(0..1), msg, Some(hint)).print();

        Issues::warn()
    } else {
        Issues::ok()
    }
}

/// checks if the identifier has snake case
pub fn check_upper_case(name: &str, loc: &TokenStream) -> Issues {
    let allupper = name
        .as_bytes()
        .iter()
        .fold(true, |acc, x| acc & !x.is_ascii_lowercase());
    if !allupper {
        let msg = format!("identifier `{}` should have an upper case name", name);
        let hint = format!(
            "convert the identifier to upper case (notice the capitalization): `{}`",
            name.to_ascii_uppercase()
        );
        VrsError::new_warn(loc.with_range(1..2), msg, Some(hint)).print();

        Issues::warn()
    } else {
        Issues::ok()
    }
}

/// checks if the identifier has snake case
pub fn check_camel_case(name: &str, loc: &TokenStream) -> Issues {
    if !name[0..1].as_bytes()[0].is_ascii_uppercase() || name.contains('_') {
        let msg = format!("identifier `{}` should be CamelCasee", name);
        let mut name = String::from(name);
        name[0..1].make_ascii_uppercase();
        let hint = format!(
            "convert the identifier to CamelCase (notice the capitalization): `{}`",
            name
        );
        VrsError::new_warn(loc.with_range(1..2), msg, Some(hint)).print();
        Issues::warn()
    } else {
        Issues::ok()
    }
}

use std::ops::Range;

pub fn check_ranges_overlap(ranges: &mut Vec<(u64, Range<u64>)>) -> Vec<(usize, usize)> {
    let mut res = Vec::new();
    if ranges.is_empty() {
        return res;
    }

    // make sure the ranges are sorted
    ranges.sort_by(|a, b| a.1.start.cmp(&b.1.start));

    // a simple overlap check: just do a linear scan
    let mut endaddr = ranges.first().unwrap().1.end;
    let mut endidx = 0;
    for (i, (_, e)) in ranges.iter().enumerate().skip(1) {
        if endaddr > e.start {
            res.push((i, endidx));
        }

        if endaddr < e.end {
            endaddr = e.end;
            endidx = i;
        }
    }

    res
}
