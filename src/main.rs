// Velosiraptor Lexer
//
//
// MIT License
//
// Copyright (c) 2021 Systopia Lab, Computer Science, University of British Columbia
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

//! Velosiraptor Compiler

// used for parsing
use clap::{App, Arg};

use simplelog::{Config, LevelFilter, SimpleLogger};

// get the parser module
use libvrc::parser::Parser;

fn parse_cmdline() -> clap::ArgMatches<'static> {
    App::new("vtrc")
        .version("0.1.0")
        .author("Reto Achermann <achreto@cs.ubc.ca>")
        .about("VelosiTransRaptor Compiler")
        .arg(
            Arg::with_name("output")
                .short("o")
                .long("output")
                .takes_value(true)
                .help("the output file"),
        )
        .arg(
            Arg::with_name("v")
                .short("v")
                .multiple(true)
                .help("Sets the level of verbosity"),
        )
        .arg(
            Arg::with_name("input")
                .help("Sets the input file to use")
                .required(true)
                .index(1),
        )
        .get_matches()
}

/// Main - entry point into the application
fn main() {
    // get the command line argumentts
    let matches = parse_cmdline();

    // setting the log level
    let filter_level = match matches.occurrences_of("v") {
        0 => LevelFilter::Warn,
        1 => LevelFilter::Info,
        2 => LevelFilter::Debug,
        _ => LevelFilter::Trace,
    };

    // initialize the logger
    SimpleLogger::init(filter_level, Config::default()).unwrap();

    // show the welcome message
    log::info!("Velosiraptor Compiler (vrc)");

    let infile = matches.value_of("input").unwrap_or("none");
    log::info!("input file: {}", infile);

    let out = matches.value_of("output").unwrap_or("<stdout>");
    log::info!("input file: {}", out);

    log::debug!("Debug output enabled");
    log::trace!("Tracing output enabled");

    // let's try to create a file parser
    let ast = match Parser::parse_file(infile) {
        Ok((ast, _)) => ast,
        Err(x) => {
            log::error!("file parsing failed");
            return;
        }
    };

    println!("{}", ast);
    // let mut parser = Parser::from_file(infile.to_string()).expect("failed to construct the parser");

    // perform checks
}

// use std::rc::Rc;
// struct Foo {
//     s : Rc<String>
// }
// struct Bar {
//     s: Rc<String>,
//     f: Foo,
// }
// impl Bar {
//     fn new() -> Self {
//         let s = Rc::new("test".to_string());
//         Bar {
//             s: s.clone(),
//             f : Foo {s: s.clone()}
//         }
//     }
// }
