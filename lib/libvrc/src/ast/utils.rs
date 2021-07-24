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

use crate::ast::AstNode;
use crate::error::VrsError;
use std::collections::HashMap;

/// drains the list and merges it into the hashmap
pub fn collect_list<T: AstNode>(list: &mut Vec<T>, hmap: &mut HashMap<String, T>) -> u32 {
    let mut errors = 0;
    for elm in list.drain(..) {
        let key = elm.name();
        match hmap.get(key) {
            Some(prev) => {
                errors = errors + 1;
                VrsError::new_double(key.to_string(), elm.loc().clone(), prev.loc().clone())
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
