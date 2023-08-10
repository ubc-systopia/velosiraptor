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
use velosiparser::{VelosiParser, VelosiParserError};

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

fn check_parse_fail(vrs: &Path, exp: Option<&Path>) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);

    if let Some(exp) = exp {
        assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());
    }

    print!("  - Parsing {path_str} ...");

    // basic import
    match VelosiParser::parse_file(path_str, exp.is_some()) {
        Ok(_p) => {
            panic!("Expected parsing to have failed");
        }
        Err(VelosiParserError::ParsingFailure { e }) => {
            println!("\n\n>>>>>>>>>>>>>>>\n{e}<<<<<<<<<<<<<<<\n");
            if let Some(exp) = exp {
                let res = fs::read_to_string(exp).expect("could not read the exected output file");

                let plain_bytes = strip_ansi_escapes::strip(e.to_string())
                    .expect("could not string the ansi escapes");

                let error_str = String::from_utf8(plain_bytes).expect("could not convert to utf8");

                assert_eq!(error_str, res);
                println!(" ok  Parsing resulted in error. (resolving imports)");
            } else {
                println!(" ok  Parsing resulted in an error. ");
            }
        }
        Err(e) => {
            println!(" fail  ({e})");
            panic!("Unexpected failure during parsing.");
        }
    }
}

/// Test basic constant definitions
#[test]
fn const_defs() {
    let vrs = Path::new("tests/vrs/consts/const_00_defs.vrs");
    let exp = Path::new("tests/vrs/consts/const_00_defs_expected.txt");
    check_parse_ok(vrs, None);
    check_parse_ok(vrs, Some(exp));
}

/// Test imported constants
#[test]
fn const_imported() {
    let vrs = Path::new("tests/vrs/consts/const_01_imported.vrs");
    let exp = Path::new("tests/vrs/consts/const_01_imported_expected.txt");
    check_parse_ok(vrs, None);
    check_parse_ok(vrs, Some(exp));
}

/// Test constants within unit context
#[test]
fn const_unit() {
    let vrs = Path::new("tests/vrs/consts/const_02_unit.vrs");
    let exp = Path::new("tests/vrs/consts/const_02_unit_expected.txt");
    check_parse_ok(vrs, None);
    check_parse_ok(vrs, Some(exp));
}

/// Test expressions with constants
#[test]
fn const_expr() {
    let vrs = Path::new("tests/vrs/consts/const_03_expr.vrs");
    let exp = Path::new("tests/vrs/consts/const_03_expr_expected.txt");
    check_parse_ok(vrs, None);
    check_parse_ok(vrs, Some(exp));
}

/// Test missing semicolon
#[test]
fn const_missing_semicolon() {
    let vrs = Path::new("tests/vrs/consts/const_04_missing_semicolon.vrs");
    let exp = Path::new("tests/vrs/consts/const_04_missing_semicolon_expected.txt");
    check_parse_fail(vrs, None);
    check_parse_fail(vrs, Some(exp));
}

/// Test missing semicolon
#[test]
fn const_missing_type() {
    let vrs = Path::new("tests/vrs/consts/const_05_missing_type.vrs");
    let exp = Path::new("tests/vrs/consts/const_05_missing_type_expected.txt");
    check_parse_fail(vrs, None);
    check_parse_fail(vrs, Some(exp));
}
