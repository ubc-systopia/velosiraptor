// Velosicomposition - Higher-Level Composition of Velosiraptor Programs
//
//
// MIT License
//
// Copyright (c) 2021, 2022, 2023 Systopia Lab, Computer Science, University of British Columbia
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

//! # Velosicomposition -- The Velosiraptor Higher-Level Composition Example Program
//!
//! This example program

use std::io;
use std::io::Read;

use clap::Parser;
use colored::*;
use simplelog::{ColorChoice, ConfigBuilder, LevelFilter, LevelPadding, TermLogger, TerminalMode};

use velosiast::{AstResult, VelosiAst};

/// the commandline arguments
#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// the input file to operate on
    infile: Option<String>,

    /// Turn debugging information on
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,
}

pub fn main() {
    // parse command line arguments
    let cli = Cli::parse();

    // setting the log level
    let filter_level = match cli.verbose {
        0 => LevelFilter::Warn,
        1 => LevelFilter::Info,
        2 => LevelFilter::Debug,
        _ => LevelFilter::Trace,
    };

    // initialize the logger
    let config = ConfigBuilder::default()
        .set_level_padding(LevelPadding::Right)
        .set_thread_level(LevelFilter::Off)
        .set_target_level(LevelFilter::Warn)
        .set_location_level(LevelFilter::Off)
        .build();

    TermLogger::init(
        filter_level,
        config,
        TerminalMode::Stdout,
        ColorChoice::Auto,
    )
    .expect("failed to setup logger");

    let ast = match cli.infile.as_deref() {
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

    let mut ast = match ast {
        AstResult::Ok(ast) => ast,
        AstResult::Issues(ast, err) => {
            eprintln!("{}: parsing warnings.\n", "warning".bold().yellow());
            eprintln!("{}", err);
            ast
        }
        AstResult::Err(err) => {
            eprintln!("{}: parsing error.\n", "error".bold().red());
            eprintln!("{}", err);
            return;
        }
    };

    log::debug!("AST:");
    log::debug!(
        "---------------------------------------------------------------------------------"
    );
    log::debug!("{}", ast);
    log::debug!(
        "---------------------------------------------------------------------------------"
    );

    velosicomposition::extract_composition(&ast);
}
