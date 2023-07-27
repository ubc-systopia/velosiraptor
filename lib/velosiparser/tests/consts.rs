// VelosiParser -- a parser for the Velosiraptor Language
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

//! # VelosiParser Tests: Example Specs

// std includes
use std::fs::{self};

use std::path::Path;

// our library
use velosiparser::VelosiParser;

fn check_parse_ok(vrs: &Path, exp: Option<&Path>) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);

    if let Some(exp) = exp {
        assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());
    }

    print!("  - Parsing {path_str} ...");

    // basic import
    match VelosiParser::parse_file(path_str, true) {
        Ok(p) => {
            println!(">>>>>>\n{p}\n<<<<<<");
            if let Some(exp) = exp {
                let res = fs::read_to_string(exp).expect("could not read the exected output file");
                assert_eq!(p.to_string(), res);
                println!(" ok. Successfully parsed. Matches expected output.");
            } else {
                println!(" ok. Successfully parsed. No comparison file given.");
            }
        }
        Err(e) => {
            println!(" fail  ({e})");
            panic!("Unexpected failure during parsing.");
        }
    }
}

/// Tests the basic import functionality
#[test]
fn const_defs() {
    let vrs = Path::new("tests/vrs/consts/const_00_defs.vrs");
    let exp = Path::new("tests/vrs/consts/const_00_defs_expected.txt");
    check_parse_ok(vrs, None);
    check_parse_ok(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn const_imported() {
    let vrs = Path::new("tests/vrs/consts/const_01_imported.vrs");
    let exp = Path::new("tests/vrs/consts/const_01_imported_expected.txt");
    check_parse_ok(vrs, None);
    check_parse_ok(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn const_unit() {
    let vrs = Path::new("tests/vrs/consts/const_02_unit.vrs");
    let exp = Path::new("tests/vrs/consts/const_02_unit_expected.txt");
    check_parse_ok(vrs, None);
    check_parse_ok(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn const_expr() {
    let vrs = Path::new("tests/vrs/consts/const_03_expr.vrs");
    let exp = Path::new("tests/vrs/consts/const_03_expr_expected.txt");
    check_parse_ok(vrs, None);
    check_parse_ok(vrs, Some(exp));
}
