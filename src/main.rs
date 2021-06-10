//! Velosiraptor Compiler

// we are using nom as the parser
extern crate nom;

// used for parsing
use clap::{App, Arg};
use log::{debug, info, trace};

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

// for reading the file
use std::fs;

/// Main - entry point into the application
fn main() {
    // get the command line argumentts
    let matches = parse_cmdline();

    // setting the log level
    match matches.occurrences_of("v") {
        0 => log::set_max_level(log::LevelFilter::Warn),
        1 => log::set_max_level(log::LevelFilter::Info),
        2 => log::set_max_level(log::LevelFilter::Debug),
        _ => log::set_max_level(log::LevelFilter::Trace),
    };

    info!("Velosiraptor Compiler (vrc)");

    let infile = matches.value_of("input").unwrap_or("none");
    info!("input file: {}", infile);

    let out = matches.value_of("output").unwrap_or("<stdout>");
    info!("input file: {}", out);

    debug!("Debug output enabled");
    trace!("Tracing output enabled");

    // let's try to create a file parser
    let file_contents = fs::read_to_string(infile).expect("failed to construct the parser");
    let mut parser = Parser::from_string(&file_contents).expect("failed to construct the parser");

    // parse the file
    parser.parse();
}
