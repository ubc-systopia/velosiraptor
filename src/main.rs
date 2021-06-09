//! Velosiraptor Compiler

// we are using nom as the parser
extern crate nom;

// used for parsing
use clap::{App, Arg};

// get the parser module
mod parser;

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

    let infile = matches.value_of("input").unwrap_or("none");
    println!("Value for out: {}", infile);

    let out = matches.value_of("output").unwrap_or("<stdout>");
    println!("Value for out: {}", out);

    // now let's try to parse the file
    let res = parser::parse_file(infile);
    match res {
        Ok(_) => println!("Parsing successfule"),
        Err(_) => println!("Parsing failed"),
    }
}
