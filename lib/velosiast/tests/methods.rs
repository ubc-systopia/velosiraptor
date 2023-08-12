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

use velosiast::{AstResult, SymbolTable, VelosiAstMethod};
use velosiparser::{parse_method, VelosiLexer};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Ok Tests
////////////////////////////////////////////////////////////////////////////////////////////////////

/// parses a method directly and creats the ast, comparing the output with the expected output
fn parse_methods_from_file_ok(vrs: &Path, exp: &Path) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);
    assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());

    print!("  - Parsing {path_str} ...");

    let mut ts = VelosiLexer::lex_file(path_str).expect("could not lex the file");

    let mut output = String::new();
    while !ts.is_empty() {
        match parse_method(ts) {
            Ok((ts_new, method)) => {
                ts = ts_new;
                let mut st = SymbolTable::new();
                match VelosiAstMethod::from_parse_tree(method, &mut st) {
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
fn parse_methods_from_file_err(vrs: &Path, exp: &Path) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);
    assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());

    print!("  - Parsing {path_str} ...");

    let mut ts = VelosiLexer::lex_file(path_str).expect("could not lex the file");

    let mut output = String::new();
    while !ts.is_empty() {
        match parse_method(ts) {
            Ok((ts_new, method)) => {
                ts = ts_new;
                let mut st = SymbolTable::new();
                match VelosiAstMethod::from_parse_tree(method, &mut st) {
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
fn parse_methods_from_file_issues(vrs: &Path, exp: &Path) {
    let path_str = vrs.to_str().unwrap();
    assert!(vrs.is_file(), "{} is not a file", path_str);
    assert!(exp.is_file(), "{} is not a file", exp.to_str().unwrap());

    print!("  - Parsing {path_str} ...");

    let mut ts = VelosiLexer::lex_file(path_str).expect("could not lex the file");

    let mut output = String::new();
    while !ts.is_empty() {
        match parse_method(ts) {
            Ok((ts_new, method)) => {
                ts = ts_new;
                let mut st = SymbolTable::new();
                match VelosiAstMethod::from_parse_tree(method, &mut st) {
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
fn methods_simple() {
    let vrs = Path::new("tests/vrs/methods/methods_00_simple.vrs");
    let exp = Path::new("tests/vrs/methods/methods_00_simple_expected.txt");
    parse_methods_from_file_ok(&vrs, &exp);
}

/// test post and pre-condition definition
#[test]
fn methods_pre_post_conditions() {
    let vrs = Path::new("tests/vrs/methods/methods_01_pre_post_conditions.vrs");
    let exp = Path::new("tests/vrs/methods/methods_01_pre_post_conditions_expected.txt");
    parse_methods_from_file_ok(&vrs, &exp);
}

/// test synth and abstract definitions
#[test]
fn methods_synth_abstract() {
    let vrs = Path::new("tests/vrs/methods/methods_02_synth_abstract.vrs");
    let exp = Path::new("tests/vrs/methods/methods_02_synth_abstract_expected.txt");
    parse_methods_from_file_ok(&vrs, &exp);
}

/// test basic interface definition
#[test]
fn methods_decorators() {
    let vrs = Path::new("tests/vrs/methods/methods_03_decorators.vrs");
    let exp = Path::new("tests/vrs/methods/methods_03_decorators_expected.txt");
    parse_methods_from_file_ok(&vrs, &exp);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Warnings
////////////////////////////////////////////////////////////////////////////////////////////////////

/// test basic interface definition
#[test]
fn methods_ident_case() {
    let vrs = Path::new("tests/vrs/methods/methods_warn_00_ident_case.vrs");
    let exp = Path::new("tests/vrs/methods/methods_warn_00_ident_case_expected.txt");
    parse_methods_from_file_issues(&vrs, &exp);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Error Cases
////////////////////////////////////////////////////////////////////////////////////////////////////

/// double definition of the parameter
#[test]
fn methods_err_double_param_definition() {
    let vrs = Path::new("tests/vrs/methods/methods_err_00_double_parameter.vrs");
    let exp = Path::new("tests/vrs/methods/methods_err_00_double_parameter_expected.txt");
    parse_methods_from_file_err(&vrs, &exp);
}

// undefined symbol in the body
#[test]
fn methods_err_undef_symbol() {
    let vrs = Path::new("tests/vrs/methods/methods_err_01_undef_symbol.vrs");
    let exp = Path::new("tests/vrs/methods/methods_err_01_undef_symbol_expected.txt");
    parse_methods_from_file_err(&vrs, &exp);
}

// return types wrong
#[test]
fn methods_err_return_type() {
    let vrs = Path::new("tests/vrs/methods/methods_err_02_wrong_return_types.vrs");
    let exp = Path::new("tests/vrs/methods/methods_err_02_wrong_return_types_expected.txt");
    parse_methods_from_file_err(&vrs, &exp);
}

// undefined symbol in the body
#[test]
fn methods_err_requires_type() {
    let vrs = Path::new("tests/vrs/methods/methods_err_03_pre_post_cond_types.vrs");
    let exp = Path::new("tests/vrs/methods/methods_err_03_pre_post_cond_types_expected.txt");
    parse_methods_from_file_err(&vrs, &exp);
}

// undefined symbol in the body
#[test]
fn methods_err_unknown_type() {
    let vrs = Path::new("tests/vrs/methods/methods_err_04_unknown_type.vrs");
    let exp = Path::new("tests/vrs/methods/methods_err_04_unknown_type_expected.txt");
    parse_methods_from_file_err(&vrs, &exp);
}
