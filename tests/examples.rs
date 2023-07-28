// VelosiParser -- a parser for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2023 Systopia Lab, Computer Science, University of British Columbia
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

use std::path::{PathBuf};

// use strip_ansi_escapes;

// our library
use velosiast::{AstResult, VelosiAst};
use velosiparser::{VelosiParser, VelosiParserError};

/// Tests the basic import functionality
#[test]
fn examples_parse() {
    let d = PathBuf::from("examples");
    for f in d.read_dir().expect("could not read example directory") {
        let vrs = f.expect("could not read directory entry").path();

        if vrs.is_dir() {
            continue;
        }

        let path_str = vrs.to_str().expect("could not create string from path");

        print!("  - Parsing {path_str} ...");

        match VelosiParser::parse_file(path_str, false) {
            Ok(_pt) => {
                println!(" ok. Successfully parsed.");
            }
            Err(VelosiParserError::LexingFailure { e }) => {
                println!(" fail  (lexer failure)");
                println!(">>>>>>\n{}\n<<<<<<", e);
                panic!("Could not parse file");
            }
            Err(VelosiParserError::ParsingFailure { e }) => {
                println!(" fail  (parser failure)");
                println!(">>>>>>\n{}\n<<<<<<", e);
            }
            Err(e) => {
                println!(" fail  (unknown error)");
                println!(">>>>>>\n{}\n<<<<<<", e);
                panic!("Could not parse file");
            }
        }
    }
}

/// Tests the basic import functionality
#[test]
fn examples_ast() {
    let d = PathBuf::from("examples");
    for f in d.read_dir().expect("could not read example directory") {
        let vrs = f.expect("could not read directory entry").path();

        if vrs.is_dir() {
            continue;
        }

        let path_str = vrs.to_str().expect("could not create string from path");

        print!("  - Parsing {path_str} ...");

        match VelosiAst::from_file(path_str) {
            AstResult::Ok(_ast) => {
                println!(" ok. Successfully created Ast.");
            }
            AstResult::Issues(_ast, e) => {
                println!(" ok  (with warningsk)");
                println!(">>>>>>\n{}\n<<<<<<", e);
                // panic!("Could not parse file");
            }
            AstResult::Err(e) => {
                println!(" fail  (expected ok)");
                println!(">>>>>>\n{e}\n<<<<<<");
                panic!("Failed to construct AST.");
            }
        }
    }
}
