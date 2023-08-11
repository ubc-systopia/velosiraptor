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

// std includes
use std::fs::{self};
use std::path::Path;

// our library
use velosiparser::{VelosiParser, VelosiParserError};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Test Utils
////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
#[allow(dead_code)]
pub fn check_parse_ok(vrs: &Path, exp: Option<&Path>) {
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
        Err(VelosiParserError::ParsingFailure { e }) => {
            println!(" fail  ({e})");
            panic!("Unexpected failure during parsing.");
        }
        Err(e) => {
            println!(" fail  ({e})");
            panic!("Unexpected failure during parsing.");
        }
    }
}

#[cfg(test)]
#[allow(dead_code)]
pub fn check_parse_fail(vrs: &Path, exp: Option<&Path>) {
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
