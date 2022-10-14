// Velosilexer -- a lexer for the Velosiraptor Language
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

//! # VelosiLexer -- The Velosiraptor Lexer Example Programm
//!
//! This example program

use std::env;
use std::io;
use std::io::Read;

use velosiparser::{VelosiParser, VelosiParserError};

pub fn main() {
    let args: Vec<String> = env::args().collect();

    let res = match args.len() {
        1 => {
            let mut buffer = String::new();
            let mut stdin = io::stdin();
            stdin
                .read_to_string(&mut buffer)
                .expect("could not read from stdin");
            VelosiParser::parse_string(buffer)
        }
        2 => VelosiParser::parse_file(&args[1]),
        _ => {
            println!("Usage: velosiparser [file]");
            println!("Usage: echo \"foo\" | velosiparser");
            return;
        }
    };

    let res = if let Ok(ps) = res {
        VelosiParser::resolve_imports(ps)
    } else {
        res
    };

    match res {
        Ok(tokens) => {
            println!("{}", tokens);
        }
        Err(VelosiParserError::ReadSourceFile { e }) => {
            println!("Failed to open the source file: {}", e);
        }

        Err(VelosiParserError::LexingFailure { e }) => {
            println!("Lexing Failure");
            println!("{}", e);
        }

        Err(VelosiParserError::ParsingFailure { e }) => {
            println!("Parsing Failure");
            println!("{}", e);
        }
        Err(VelosiParserError::ImportFailure { e }) => {
            println!("Import resolution failure");
            println!("{}", e);
        }
    }
}
