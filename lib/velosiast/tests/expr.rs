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

//! # VelosiAst Tests: Methods

// std includes
use std::fs;
use std::path::Path;

mod utils;

use velosiast::ast::{VelosiAstExpr, VelosiAstTypeInfo};
use velosiast::{Symbol, SymbolTable};
use velosiparser::{parse_expr, VelosiLexer};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Ok Tests
////////////////////////////////////////////////////////////////////////////////////////////////////

// creates a
fn create_symbol_table() -> SymbolTable {
    let mut st = SymbolTable::with_context("test");

    let _ = st.insert(Symbol::new_param(
        String::from("mybool"),
        VelosiAstTypeInfo::Bool,
    ));

    let _ = st.insert(Symbol::new_param(
        String::from("a"),
        VelosiAstTypeInfo::Integer,
    ));

    let _ = st.insert(Symbol::new_param(
        String::from("b"),
        VelosiAstTypeInfo::Integer,
    ));

    let _ = st.insert(Symbol::new_param(
        String::from("c"),
        VelosiAstTypeInfo::Integer,
    ));

    st
}

/// parses a expr directly and creats the ast, comparing the output with the expected output
fn parse_expr_from_file_ok(vrs: &Path, exp: &Path) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);
    assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());

    print!("  - Parsing {path_str} ...");

    let mut ts = VelosiLexer::lex_file(path_str).expect("could not lex the file");

    let mut output = String::new();
    while !ts.is_empty() {
        match parse_expr(ts) {
            Ok((ts_new, expr)) => {
                ts = ts_new;
                ts.pos_next(); // skip over the ;
                let mut st = create_symbol_table();
                utils::check_result_expect_ok(
                    &mut output,
                    &VelosiAstExpr::from_parse_tree(expr, &mut st),
                );
            }
            e => {
                println!("parsing failed: {:?}", e);
                panic!("failure while testing: unexpected parsing result\n");
            }
        }
    }

    println!(">>>>>>\n{output}\n<<<<<<");

    let expected = fs::read_to_string(exp).expect("could not read the exected output file");
    assert_eq!(output.trim_end(), expected.trim_end());
}

/// parses a expr directly and creats the ast, comparing the output with the expected output
fn parse_expr_from_file_err(vrs: &Path, exp: &Path) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);
    assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());

    print!("  - Parsing {path_str} ...");

    let mut ts = VelosiLexer::lex_file(path_str).expect("could not lex the file");

    let mut output = String::new();
    while !ts.is_empty() {
        match parse_expr(ts) {
            Ok((ts_new, expr)) => {
                ts = ts_new;
                ts.pos_next(); // skip over the ;
                let mut st = create_symbol_table();
                utils::check_result_expect_errors(
                    &mut output,
                    &VelosiAstExpr::from_parse_tree(expr, &mut st),
                );
            }
            e => {
                println!("parsing failed: {:?}", e);
                panic!("failure while testing: unexpected parsing result\n");
            }
        }
    }

    println!(">>>>>>\n{output}\n<<<<<<");

    let expected = fs::read_to_string(exp).expect("could not read the exected output file");
    assert_eq!(output.trim_end(), expected.trim_end());
}

/// parses a expr directly and creats the ast, comparing the output with the expected output
fn parse_expr_from_file_issues(vrs: &Path, exp: &Path) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);
    assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());

    print!("  - Parsing {path_str} ...");

    let mut ts = VelosiLexer::lex_file(path_str).expect("could not lex the file");

    let mut output = String::new();
    while !ts.is_empty() {
        match parse_expr(ts) {
            Ok((ts_new, expr)) => {
                ts = ts_new;
                ts.pos_next(); // skip over the ;
                let mut st = create_symbol_table();
                utils::check_result_expect_warnings(
                    &mut output,
                    &VelosiAstExpr::from_parse_tree(expr, &mut st),
                );
            }
            e => {
                println!("parsing failed: {:?}", e);
                panic!("failure while testing: unexpected parsing result\n");
            }
        }
    }

    println!(">>>>>>\n{output}\n<<<<<<");

    let expected = fs::read_to_string(exp).expect("could not read the exected output file");
    assert_eq!(output.trim_end(), expected.trim_end());
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Success Cases
////////////////////////////////////////////////////////////////////////////////////////////////////

/// test basic expr definition
#[test]
fn expr_ok_simple() {
    let vrs = Path::new("tests/vrs/expr/expr_ok_00_simple.vrs");
    let exp = Path::new("tests/vrs/expr/expr_ok_00_simple_expected.txt");
    parse_expr_from_file_ok(&vrs, &exp);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Warnings
////////////////////////////////////////////////////////////////////////////////////////////////////

/// test basic interface definition
#[test]
fn expr_warn_ident_case() {
    let vrs = Path::new("tests/vrs/expr/expr_warn_00_const_if.vrs");
    let exp = Path::new("tests/vrs/expr/expr_warn_00_const_if_expected.txt");
    parse_expr_from_file_issues(&vrs, &exp);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Error Cases
////////////////////////////////////////////////////////////////////////////////////////////////////

/// double definition of the parameter
#[test]
fn expr_err_double_param_definition() {
    let vrs = Path::new("tests/vrs/expr/expr_err_00_types.vrs");
    let exp = Path::new("tests/vrs/expr/expr_err_00_types_expected.txt");
    parse_expr_from_file_err(&vrs, &exp);
}
