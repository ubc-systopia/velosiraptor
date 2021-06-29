//! Velosiraptor Compiler

// we are using nom as the parser
extern crate nom;

// used for parsing
use clap::{App, Arg};

use simplelog::{Config, LevelFilter, SimpleLogger};

// get the parser module
mod parser;
use parser::Parser;

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
    let mut parser = Parser::from_file(infile.to_string()).expect("failed to construct the parser");

    // parse the file
    let err = parser.parse();
    if err.is_err() {
        log::error!("Parsing failed.");
    }
    // resolve the import statements
    let err = parser.resolve_imports();
    if err.is_err() {
        log::error!("Failed to resolve imports.");
    }

    // perform checks
}
