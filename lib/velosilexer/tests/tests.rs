// VelosiParser -- a parser for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2021-2023 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiParser Tests

// std includes
use std::fs::{self};

use std::path::Path;

// our library
use velosilexer::{VelosiLexer, VelosiLexerError};

fn check_lex_ok(vrs: &Path, exp: Option<&Path>) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);

    if let Some(exp) = exp {
        assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());
    }

    print!("  - Lexing {path_str} ...");

    // basic import
    match VelosiLexer::lex_file(path_str) {
        Ok(p) => {
            if let Some(exp) = exp {
                let res = fs::read_to_string(exp).expect("could not read the exected output file");
                assert_eq!(p.to_string(), res);
                println!(" ok. Successfully lexed. Matches expected output.");
            } else {
                println!(" ok. Successfully lexed. No comparison file given.");
            }
        }
        Err(VelosiLexerError::LexingFailure { r }) => {
            println!(" fail  ({r})");
            panic!("Unexpected failure during parsing.");
        }
        Err(e) => {
            println!(" fail  ({e})");
            panic!("Unexpected failure during parsing.");
        }
    }
}

fn check_lex_fail(vrs: &Path, exp: Option<&Path>) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);

    let res = if let Some(exp) = exp {
        assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());
        Some(fs::read_to_string(exp).expect("could not read the exected output file"))
    } else {
        None
    };

    print!("  - Lexing {path_str} ...");

    // basic import
    match VelosiLexer::lex_file(path_str) {
        Ok(p) => {
            println!(" FAILED.");
            println!("{p}");
            panic!("Expected failure during lexing.")
        }
        Err(VelosiLexerError::LexingFailure { r }) => {
            if let Some(res) = res {
                let plain_bytes = strip_ansi_escapes::strip(r.to_string())
                    .expect("could not string the ansi escapes");

                let error_str = String::from_utf8(plain_bytes).expect("could not convert to utf8");

                assert_eq!(error_str, res);
                println!(" ok (matched output)");
            } else {
                println!(" ok (no comparison");
            }
        }
        Err(e) => {
            println!(" ok  ({e})");
            panic!("Unexpected failure during parsing.");
        }
    }
}

/// Tests the basic import functionality
#[test]
fn empty_file() {
    let vrs = Path::new("tests/vrs/lex_01_empty_file.vrs");
    let exp = Path::new("tests/vrs/lex_01_empty_file_expect.txt");
    check_lex_ok(vrs, None);
    check_lex_ok(vrs, Some(exp));
}

#[test]
fn whitespace() {
    let vrs = Path::new("tests/vrs/lex_02_whitespace.vrs");
    let exp = Path::new("tests/vrs/lex_02_whitespace_expect.txt");
    check_lex_ok(vrs, None);
    check_lex_ok(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn comments() {
    let vrs = Path::new("tests/vrs/lex_03_comments.vrs");
    let exp = Path::new("tests/vrs/lex_03_comments_expect.txt");
    check_lex_ok(vrs, None);
    check_lex_ok(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn comments_not_closed() {
    let vrs = Path::new("tests/vrs/lex_04_comments_fail.vrs");
    let exp = Path::new("tests/vrs/lex_04_comments_fail_expect.txt");
    check_lex_fail(vrs, None);
    check_lex_fail(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn invalid_token() {
    let vrs = Path::new("tests/vrs/lex_05_invalid_token.vrs");
    let exp = Path::new("tests/vrs/lex_05_invalid_token_expect.txt");
    check_lex_fail(vrs, None);
    check_lex_fail(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn numbers() {
    let vrs = Path::new("tests/vrs/lex_06_numbers.vrs");
    let exp = Path::new("tests/vrs/lex_06_numbers_expect.txt");
    check_lex_ok(vrs, None);
    check_lex_ok(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn identifiers() {
    let vrs = Path::new("tests/vrs/lex_07_identifiers.vrs");
    let exp = Path::new("tests/vrs/lex_07_identifiers_expect.txt");
    check_lex_ok(vrs, None);
    check_lex_ok(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn invalid_identifiers() {
    let vrs = Path::new("tests/vrs/lex_08_invalid_identifiers.vrs");
    let exp = Path::new("tests/vrs/lex_08_invalid_identifiers_expect.txt");
    check_lex_fail(vrs, None);
    check_lex_fail(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn expressions() {
    let vrs = Path::new("tests/vrs/lex_09_expressions.vrs");
    let exp = Path::new("tests/vrs/lex_09_expressions_expect.txt");
    check_lex_ok(vrs, None);
    check_lex_ok(vrs, Some(exp));
}
