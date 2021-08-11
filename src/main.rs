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

use clap::{App, Arg};
use colored::*;
use simplelog::{Config, LevelFilter, SimpleLogger};
use std::process::exit;

// get the parser module
use libvrc::ast::{AstError, Issues};
use libvrc::parser::{Parser, ParserError};

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
            Arg::with_name("error")
                .short("e")
                .long("Werror")
                .takes_value(true)
                .help("Treat warnings to errors."),
        )
        .arg(
            Arg::with_name("input")
                .help("Sets the input file to use")
                .required(true)
                .index(1),
        )
        .get_matches()
}
use libvrc::error::{ErrorLocation, VrsError};
fn print_errors_and_exit<I: ErrorLocation + std::fmt::Display>(
    msg: &str,
    err: VrsError<I>,
    target: &str,
    cnt: Issues,
) {
    err.print();
    eprintln!("{}{}{}.\n", "error".bold().red(), ": ".bold(), msg.bold());
    abort(target, cnt)
}

fn abort(target: &str, cnt: Issues) {
    let msg = format!(": aborting due to previous {} error(s)", cnt.errors);
    eprint!("{}{}", "error".bold().red(), msg.bold());
    if cnt.warnings > 0 {
        let msg = format!(", and {} warnings emitted", cnt.warnings);
        eprintln!("{}\n", msg.bold());
    } else {
        eprintln!(); // add some newline
    }
    eprintln!(
        "{}: could not compile `{}`.\n",
        "error".bold().red(),
        target
    );
    exit(-1);
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

    // print the start message
    eprintln!(
        "{:>8}: Velosiraptor Compiler (vrc)...\n",
        "start".bold().green(),
    );

    let infile = matches.value_of("input").unwrap_or("none");
    log::info!("input file: {}", infile);

    let outfile = matches.value_of("output").unwrap_or("<stdout>");
    log::info!("output file: {}", outfile);

    log::debug!("Debug output enabled");
    log::trace!("Tracing output enabled");

    log::info!("==== PARSING STAGE ====");

    // ===========================================================================================
    // Step 1: Parse the input file
    // ===========================================================================================

    eprintln!("{:>8}: {}...\n", "parse".bold().green(), infile);

    // let's try to create a file parser
    let mut ast = match Parser::parse_file(infile) {
        Ok((ast, _)) => ast,
        Err(ParserError::LexerFailure { error }) => {
            print_errors_and_exit("during lexing of the file", error, infile, Issues::err());
            return;
        }
        Err(ParserError::ParserFailure { error }) => {
            print_errors_and_exit("during parsing of the file", error, infile, Issues::err());
            return;
        }
        Err(ParserError::ParserIncomplete { error }) => {
            print_errors_and_exit(
                "unexpected junk at the end of the file",
                error,
                infile,
                Issues::err(),
            );
            return;
        }
        Err(_) => {
            abort(infile, Issues::err());
            return;
        }
    };

    log::info!("AST:");
    log::info!("----------------------------");
    log::info!("{}", ast);
    log::info!("----------------------------");

    // ===========================================================================================
    // Step 2: Resolve the imports and merge ASTs
    // ===========================================================================================

    match ast.resolve_imports() {
        Ok(()) => (),
        Err(AstError::ImportError { e }) => {
            print_errors_and_exit("failed resolving the imports", e, infile, Issues::err());
            return;
        }
        Err(AstError::MergeError { i }) => {
            eprintln!(
                "{}{}.\n",
                "error".bold().red(),
                ": during merging of the ASTs".bold()
            );
            abort(infile, i)
        }
        _ => {
            abort(infile, Issues::err());
            return;
        }
    };

    eprintln!(
        "{:>8}: resolved {} import(s)..\n",
        "import".bold().green(),
        ast.imports.len(),
    );

    log::info!("AST:");
    log::info!("----------------------------");
    log::info!("{}", ast);
    log::info!("----------------------------");

    log::info!("==== CHECKING STAGE ====");

    // ===========================================================================================
    // Step 3: Build Symboltable
    // ===========================================================================================

    let mut symtab = match ast.build_symboltable() {
        Ok(symtab) => symtab,
        Err(AstError::SymTabError { i }) => {
            eprintln!(
                "{}{}.\n",
                "error".bold().red(),
                ": during building of the symbol table".bold()
            );
            abort(infile, i);
            return;
        }
        _ => {
            abort(infile, Issues::err());
            return;
        }
    };

    // build the symbolt table
    eprintln!(
        "{:>8}: created symboltable with {} symbols\n",
        "symtab".bold().green(),
        symtab.count()
    );

    log::info!("Symbol Table:");
    log::info!("----------------------------");
    log::info!("\n{}", symtab);
    log::info!("----------------------------");

    // ===========================================================================================
    // Step 4: Consistency Checks
    // ===========================================================================================

    let issues = Issues::ok();

    eprintln!(
        "{:>8}: performing consistency check...\n",
        "check".bold().green(),
    );

    let issues = match ast.check_consistency(&mut symtab) {
        Ok(i) => issues + i,
        Err(AstError::CheckError { i }) => {
            //            matches.value_of("input").unwrap_or("none");
            abort(infile, i);
            return;
        }
        _ => {
            abort(infile, Issues::err());
            return;
        }
    };

    // ===========================================================================================
    // Step 5: Transform AST
    // ===========================================================================================

    let issues = match ast.apply_transformations() {
        Ok(i) => issues + i,
        Err(_) => {
            abort(infile, Issues::err());
            return;
        }
    };

    // ===========================================================================================
    // Step 6: Generate OS code
    // ===========================================================================================

    if issues.is_err() {
        abort(infile, issues);
        return;
    }

    log::info!("==== CODE GENERATION STAGE ====");

    // so things should be fine, we can now go and generate stuff

    // generate the raw interface files: this is the "language" to interface
    eprintln!(
        "{:>8}: generating interface files...\n",
        "generate".bold().green(),
    );

    // generate the unit files that use the interface files
    eprintln!(
        "{:>8}: generating unit files...\n",
        "generate".bold().green(),
    );

    // ===========================================================================================
    // Step 6: Generate simulator modules
    // ===========================================================================================

    // we can generate some modules
    eprintln!(
        "{:>8}: generating Arm FastModels modules...\n",
        "generate".bold().green(),
    );

    if issues.warnings > 0 {
        let msg = format!("{} warning(s) emitted", issues.warnings);
        eprintln!("{}{}.\n", "warning: ".bold().yellow(), msg.bold());
    }

    // ok all done.
    eprintln!("{:>8}: ...\n", "finished".bold().green());
}
