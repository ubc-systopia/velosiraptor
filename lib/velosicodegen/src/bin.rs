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
use std::time::Instant;

use clap::{arg, command};
use simplelog::{ColorChoice, ConfigBuilder, LevelFilter, LevelPadding, TermLogger, TerminalMode};

use velosiast::{AstResult, VelosiAst};
use velosisynth::Z3Synth;

pub fn main() {
    // get the command line argumentts
    let matches = command!() // requires `cargo` feature
        .arg(arg!(
            -v --verbose ... "Turn debugging verbosity on"
        ))
        .arg(arg!(-c --cores <VALUE>).default_value("1"))
        .arg(arg!(-s --synth <VALUE>).default_value("all"))
        .arg(arg!([fname] "Optional name to operate on"))
        .get_matches();

    let filter_level = match matches
        .get_one::<u8>("verbose")
        .expect("Count's are defaulted")
    {
        0 => LevelFilter::Warn,
        1 => LevelFilter::Info,
        2 => LevelFilter::Debug,
        _ => LevelFilter::Trace,
    };

    let config = ConfigBuilder::default()
        .set_level_padding(LevelPadding::Right)
        .set_thread_level(LevelFilter::Off)
        .set_target_level(LevelFilter::Warn)
        .set_location_level(LevelFilter::Off)
        .build();

    let ncores = matches
        .get_one::<String>("cores")
        .unwrap()
        .parse::<usize>()
        .unwrap();

    TermLogger::init(
        filter_level,
        config,
        TerminalMode::Stdout,
        ColorChoice::Auto,
    )
    .expect("failed to setup logger");

    let t_start = Instant::now();

    let ast = match matches.get_one::<String>("fname") {
        Some(filename) => VelosiAst::from_file(filename),
        None => {
            let mut buffer = String::new();
            let mut stdin = io::stdin();
            stdin
                .read_to_string(&mut buffer)
                .expect("could not read from stdin");
            VelosiAst::from_string(buffer)
        }
    };

    let _ast = match ast {
        AstResult::Ok(ast) => {
            // println!("{}", ast);
            ast
        }
        AstResult::Issues(ast, err) => {
            // println!("{}", ast);
            println!("{}", err);
            ast
        }
        AstResult::Err(err) => {
            println!("{}", err);
            return;
        }
    };

    // TODO: finish this

}
