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

//! # VelosiAst -- The Velosiraptor Ast Example Programm
//!
//! This example program

use std::env;
use std::io;
use std::io::Read;

use velosiast::{AstResult, VelosiAst};

pub fn main() {
    let args: Vec<String> = env::args().collect();

    let ast = match args.len() {
        1 => {
            let mut buffer = String::new();
            let mut stdin = io::stdin();
            stdin
                .read_to_string(&mut buffer)
                .expect("could not read from stdin");
            VelosiAst::from_string(buffer)
        }
        2 => VelosiAst::from_file(&args[1]),
        _ => {
            println!("Usage: velosiast [file]");
            println!("Usage: echo \"foo\" | velosiparser");
            return;
        }
    };

    match ast {
        AstResult::Ok(ast) => println!("{}", ast),
        AstResult::Issues(ast, err) => {
            println!("{}", ast);
            println!("{}", err);
        }
        AstResult::Err(err) => println!("{}", err),
    }
}
