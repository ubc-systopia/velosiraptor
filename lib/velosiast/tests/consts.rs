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

use strip_ansi_escapes;

// our library
use velosiast::{AstResult, VelosiAst};

fn check_ast_ok(vrs: &Path, exp: Option<&Path>) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);

    if let Some(exp) = exp {
        assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());
    }

    print!("  - Check AST of {path_str} ...");

    // basic import
    match VelosiAst::from_file(path_str) {
        AstResult::Ok(ast) => {
            println!(">>>>>>\n{ast}\n<<<<<<");
            if let Some(exp) = exp {
                let res = fs::read_to_string(exp).expect("could not read the exected output file");
                assert_eq!(ast.to_string(), res);
                println!(" ok. Successfully parsed. Matches expected output.");
            } else {
                println!(" ok. Successfully parsed. No comparison file given.");
            }
        }
        AstResult::Issues(ast, e) => {
            println!(" fail  (expected ok)");
            println!(">>>>>>\n{ast}\n<<<<<<");
            println!(">>>>>>\n{e}\n<<<<<<");
            panic!("Unexpected warnings during parsing.");
        }
        AstResult::Err(e) => {
            println!(" fail  (expected ok)");
            println!(">>>>>>\n{e}\n<<<<<<");
            panic!("Unexpected failure during parsing.");
        }
    }
}

fn check_ast_warn(vrs: &Path, exp: Option<&Path>) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);

    if let Some(exp) = exp {
        assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());
    }

    print!("  - Check AST of {path_str} ...");

    // basic import
    match VelosiAst::from_file(path_str) {
        AstResult::Ok(ast) => {
            println!(" fail  (expected warnings)");
            println!(">>>>>>\n{ast}\n<<<<<<");
            panic!("Expected errors.");
        }
        AstResult::Issues(ast, e) => {
            if let Some(exp) = exp {
                let res = fs::read_to_string(exp).expect("could not read the exected output file");

                let plain_bytes = strip_ansi_escapes::strip(e.to_string())
                    .expect("could not string the ansi escapes");

                let error_str = String::from_utf8(plain_bytes).expect("could not convert to utf8");
                let mut parsed = ast.to_string();
                parsed.push_str("\n########################################################\n\n");
                parsed.push_str(&error_str);

                println!(">>>>>>\n{parsed}\n<<<<<<");

                assert_eq!(parsed, res);
                println!(" ok. Successfully parsed. Matches expected output.");
            } else {
                println!(" ok. Successfully parsed. No comparison file given.");
            }
        }
        AstResult::Err(e) => {
            println!(" fail  (expected warnings)");
            println!(">>>>>>\n{e}\n<<<<<<");
            panic!("Unexpected failure during parsing.");
        }
    }
}

fn check_ast_err(vrs: &Path, exp: Option<&Path>) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);

    if let Some(exp) = exp {
        assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());
    }

    print!("  - Check AST of {path_str} ...");

    // basic import
    match VelosiAst::from_file(path_str) {
        AstResult::Ok(ast) => {
            println!(" fail  (expected errors)");
            println!(">>>>>>\n{ast}\n<<<<<<");
            panic!("Expected errors.");
        }
        AstResult::Issues(ast, e) => {
            println!(" fail  (expected errors)");
            println!(">>>>>>\n{ast}\n<<<<<<");
            println!(">>>>>>\n{e}\n<<<<<<");
            panic!("Expected errors.");
        }
        AstResult::Err(e) => {
            println!(" ok  (expected errors)");
            println!(">>>>>>\n{e}\n<<<<<<");

            if let Some(exp) = exp {
                let res = fs::read_to_string(exp).expect("could not read the exected output file");

                let plain_bytes = strip_ansi_escapes::strip(e.to_string())
                    .expect("could not string the ansi escapes");

                let error_str = String::from_utf8(plain_bytes).expect("could not convert to utf8");

                assert_eq!(error_str, res);
                println!(" ok. Successfully parsed. Matches expected output.");
            } else {
                println!(" ok. Successfully parsed. No comparison file given.");
            }
        }
    }
}

/// Tests the basic import functionality
#[test]
fn const_defs() {
    let vrs = Path::new("tests/vrs/consts/const_00_defs.vrs");
    let exp = Path::new("tests/vrs/consts/const_00_defs_expected.txt");
    check_ast_ok(vrs, None);
    check_ast_ok(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn const_imported() {
    let vrs = Path::new("tests/vrs/consts/const_01_imported.vrs");
    let exp = Path::new("tests/vrs/consts/const_01_imported_expected.txt");
    check_ast_ok(vrs, None);
    check_ast_ok(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn const_warning() {
    let vrs = Path::new("tests/vrs/consts/const_02_warning.vrs");
    let exp = Path::new("tests/vrs/consts/const_02_warning_expected.txt");
    check_ast_warn(vrs, None);
    check_ast_warn(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn const_errors() {
    let vrs = Path::new("tests/vrs/consts/const_03_errors.vrs");
    let exp = Path::new("tests/vrs/consts/const_03_errors_expected.txt");
    check_ast_err(vrs, None);
    check_ast_err(vrs, Some(exp));
}

/// Tests the basic import functionality
#[test]
fn const_import_doubledef() {
    let vrs = Path::new("tests/vrs/consts/const_04_import_doubledef.vrs");
    let exp = Path::new("tests/vrs/consts/const_04_import_doubledef_expected.txt");
    check_ast_err(vrs, None);
    check_ast_err(vrs, Some(exp));
}
