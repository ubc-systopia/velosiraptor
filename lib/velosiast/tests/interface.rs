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

use velosiast::ast::{VelosiAstInterface, VelosiAstTypeInfo};
use velosiast::{AstResult, Symbol, SymbolTable};
use velosiparser::{parse_interface, VelosiLexer};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Test Helpers
////////////////////////////////////////////////////////////////////////////////////////////////////

// creates a
fn create_symbol_table() -> SymbolTable {
    let mut st = SymbolTable::new();

    let _ = st.insert(Symbol::new_param(
        String::from("base"),
        VelosiAstTypeInfo::GenAddr,
    ));
    st
}

/// parses a method directly and creats the ast, comparing the output with the expected output
fn parse_interface_from_file_ok(vrs: &Path, exp: &Path) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);
    assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());

    print!("  - Parsing {path_str} ...");

    let mut ts = VelosiLexer::lex_file(path_str).expect("could not lex the file");

    let mut output = String::new();
    while !ts.is_empty() {
        match parse_interface(ts) {
            Ok((ts_new, method)) => {
                ts = ts_new;
                let mut st = create_symbol_table();
                match VelosiAstInterface::from_parse_tree(method, &mut st) {
                    AstResult::Ok(ast) => {
                        println!(" ok. Successfully parsed.");
                        println!(">>>>>>\n{ast}\n<<<<<<");
                        output
                            .push_str(&format!("{}\n\n@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n\n", ast));
                    }
                    AstResult::Issues(ast, issues) => {
                        println!(" fail  (issues)");
                        println!(">>>>>>\n{ast}\n<<<<<<");
                        println!(">>>>>>\n{issues}\n<<<<<<");
                        panic!("Unexpected issues during AST construction");
                    }
                    AstResult::Err(err) => {
                        println!(" fail  (errors)");
                        println!(">>>>>>\n{err}\n<<<<<<");
                        panic!("Unexpected error during AST construction.");
                    }
                }
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

/// parses a method directly and creats the ast, comparing the output with the expected output
fn parse_interface_from_file_err(vrs: &Path, exp: &Path) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);
    assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());

    print!("  - Parsing {path_str} ...");

    let mut ts = VelosiLexer::lex_file(path_str).expect("could not lex the file");

    let mut output = String::new();
    while !ts.is_empty() {
        match parse_interface(ts) {
            Ok((ts_new, method)) => {
                ts = ts_new;
                let mut st = create_symbol_table();
                match VelosiAstInterface::from_parse_tree(method, &mut st) {
                    AstResult::Ok(ast) => {
                        println!(" fail  (unexpected successfully parsed)");
                        println!(">>>>>>\n{ast}\n<<<<<<");
                        panic!("Unexpected success during AST construction.");
                    }
                    AstResult::Issues(ast, issues) => {
                        if issues.has_errors() {
                            println!(" ok  (expected error)");
                            println!(">>>>>>\n{issues}\n<<<<<<");
                            output.push_str(&format!(
                                "{}\n\n@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n\n",
                                utils::strip_color(issues.to_string())
                            ));
                        } else {
                            println!(" fail  (issues)");
                            println!(">>>>>>\n{ast}\n<<<<<<");
                            println!(">>>>>>\n{issues}\n<<<<<<");
                            panic!("Unexpected issues during AST construction");
                        }
                    }
                    AstResult::Err(err) => {
                        println!(" fail  (unexpected fatal error)");
                        println!(">>>>>>\n{err}\n<<<<<<");
                        panic!("Unexpected fatal error during AST construction.");
                    }
                }
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

/// parses a method directly and creats the ast, comparing the output with the expected output
fn parse_interface_from_file_issues(vrs: &Path, exp: &Path) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);
    assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());

    print!("  - Parsing {path_str} ...");

    let mut ts = VelosiLexer::lex_file(path_str).expect("could not lex the file");

    let mut output = String::new();
    while !ts.is_empty() {
        match parse_interface(ts) {
            Ok((ts_new, method)) => {
                ts = ts_new;
                let mut st = create_symbol_table();
                match VelosiAstInterface::from_parse_tree(method, &mut st) {
                    AstResult::Ok(ast) => {
                        println!(" fail  (unexpected successfully parsed)");
                        println!(">>>>>>\n{ast}\n<<<<<<");
                        panic!("Unexpected success during AST construction.");
                    }
                    AstResult::Issues(ast, issues) => {
                        if issues.has_errors() {
                            println!(" fail  (issues)");
                            println!(">>>>>>\n{issues}\n<<<<<<");
                            panic!("Unexpected errors during AST construction");
                        } else {
                            println!(" ok  (expected issues)");
                            println!(">>>>>>\n{ast}\n<<<<<<");
                            println!(">>>>>>\n{issues}\n<<<<<<");

                            let error_str = utils::strip_color(issues.to_string());
                            output.push_str(
                                format!("{ast}\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n{error_str}")
                                    .as_str(),
                            );
                            output.push_str("\n\n@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n\n");
                        }
                    }
                    AstResult::Err(err) => {
                        println!(" fail  (unexpected fatal error)");
                        println!(">>>>>>\n{err}\n<<<<<<");
                        panic!("Unexpected fatal error during AST construction.");
                    }
                }
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

/// test basic method definition
#[test]
fn interface_simple() {
    let vrs = Path::new("tests/vrs/interface/interface_ok_00_basic_def.vrs");
    let exp = Path::new("tests/vrs/interface/interface_ok_00_basic_def_expected.txt");
    parse_interface_from_file_ok(&vrs, &exp);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Warnings
////////////////////////////////////////////////////////////////////////////////////////////////////

/// test basic interface definition
#[test]
fn interface_ident_case() {
    let vrs = Path::new("tests/vrs/interface/interface_warn_00_ident_case.vrs");
    let exp = Path::new("tests/vrs/interface/interface_warn_00_ident_case_expected.txt");
    parse_interface_from_file_issues(&vrs, &exp);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Error Cases
////////////////////////////////////////////////////////////////////////////////////////////////////

/// double definition of the parameter
#[test]
fn interface_err_double_param_definition() {
    let vrs = Path::new("tests/vrs/interface/interface_err_00_double_parameter.vrs");
    let exp = Path::new("tests/vrs/interface/interface_err_00_double_parameter_expected.txt");
    parse_interface_from_file_err(&vrs, &exp);
}
