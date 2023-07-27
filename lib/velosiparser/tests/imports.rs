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

fn check_parse_circular_fail(vrs: &Path, exp: Option<&Path>) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);

    if let Some(exp) = exp {
        assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());
    }

    print!("  - Parsing {path_str} ...");

    // basic import
    match VelosiParser::parse_file(path_str, exp.is_some()) {
        Ok(_p) => {
            if exp.is_none() {
                println!(" ok  Successfully parsed. (not resolving imports)");
            } else {
                println!(" fail  Successfully parsed a circular import.");
                panic!("Expected a circular import error but got a successful parse.");
            }
        }
        Err(VelosiParserError::ImportFailure { e }) => {
            println!("{e}");

            if let Some(exp) = exp {
                let res = fs::read_to_string(exp).expect("could not read the exected output file");

                let plain_bytes = strip_ansi_escapes::strip(e.to_string())
                    .expect("could not string the ansi escapes");

                let error_str = String::from_utf8(plain_bytes).expect("could not convert to utf8");

                assert_eq!(error_str, res);
                println!(" ok  Parsing resulted in error. (resolving imports)");
            } else {
                println!(" fail  Parsing resulted in an error. ");
                panic!("{}", e);
            }
        }
        Err(VelosiParserError::LexingFailure { e }) => {
            println!("{e}");
            if let Some(_exp) = exp {
            } else {
                println!(" fail  Parsing resulted in an error. ");
                panic!("{}", e);
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
fn basic_import() {
    let vrs = Path::new("tests/vrs/imports/import_00_basic.vrs");
    let exp = Path::new("tests/vrs/imports/import_00_basic_expect.txt");
    check_parse_ok(vrs, None);
    check_parse_ok(vrs, Some(exp));
}

/// Tests multiple import functionality
#[test]
fn multi_import() {
    let vrs = Path::new("tests/vrs/imports/import_01_multi.vrs");
    let exp = Path::new("tests/vrs/imports/import_01_multi_expect.txt");
    check_parse_ok(vrs, None);
    check_parse_ok(vrs, Some(exp));
}

/// Tests recursive import functionality
#[test]
fn recursive_import() {
    let vrs = Path::new("tests/vrs/imports/import_02_recursive.vrs");
    let exp = Path::new("tests/vrs/imports/import_02_recursive_expect.txt");
    check_parse_ok(vrs, None);
    check_parse_ok(vrs, Some(exp));
}

/// theres the diamond import
#[test]
fn diamond_import() {
    let vrs = Path::new("tests/vrs/imports/import_03_diamond.vrs");
    let exp = Path::new("tests/vrs/imports/import_03_diamond_expect.txt");
    check_parse_ok(vrs, None);
    check_parse_ok(vrs, Some(exp));
}

/// theres the diamond import
#[test]
fn non_existing_import() {
    let vrs = Path::new("tests/vrs/imports/import_04_non_existing.vrs");
    let exp = Path::new("tests/vrs/imports/import_04_non_existing_expect.txt");
    check_parse_circular_fail(vrs, None);
    check_parse_circular_fail(vrs, Some(exp));
}

/// theres the diamond import
#[test]
fn recursive_non_existing_import() {
    let vrs = Path::new("tests/vrs/imports/import_05_recursive_non_existing.vrs");
    let exp = Path::new("tests/vrs/imports/import_05_recursive_non_existing_expect.txt");
    check_parse_circular_fail(vrs, None);
    check_parse_circular_fail(vrs, Some(exp));
}

/// tests whether self circular imports are detected
#[test]
fn self_circular_import() {
    let vrs = Path::new("tests/vrs/imports/import_06_self_circular.vrs");
    let exp = Path::new("tests/vrs/imports/import_06_self_circular_expect.txt");
    check_parse_circular_fail(vrs, None);
    check_parse_circular_fail(vrs, Some(exp));
}

/// tests whether self circular imports are detected
#[test]
fn circular_import() {
    let vrs = Path::new("tests/vrs/imports/import_07_circular.vrs");
    let exp = Path::new("tests/vrs/imports/import_07_circular_expect.txt");
    check_parse_circular_fail(vrs, None);
    check_parse_circular_fail(vrs, Some(exp));
}

/// tests whether self circular imports are detected
#[test]
fn double_import() {
    let vrs = Path::new("tests/vrs/imports/import_08_double.vrs");
    let exp = Path::new("tests/vrs/imports/import_08_double_expect.txt");
    check_parse_circular_fail(vrs, None);
    check_parse_circular_fail(vrs, Some(exp));
}
