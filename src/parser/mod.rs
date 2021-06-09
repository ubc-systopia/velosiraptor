//! Velosiraptor Compiler

// for reading the file
use std::fs;

// the used nom componets
// use nom::{
//     branch::alt,
//     bytes::complete::{is_a, tag},
//     character::complete::multispace0,
//     error::ParseError,
//     multi::many0,
//     sequence::delimited,
//     IResult,
// };

mod comments;
mod tokens;
use comments::{blockcomment, comment};

use custom_error::custom_error;

use log::{debug, error, info};

use std::collections::HashMap;

custom_error! {pub ParserError
  ReadSourceFile{ file: String } = "Unknown vmxnet3 device/version",
}

pub struct Parser {
    /// the filename that is being parser
    filename: String,

    /// the source code to be parser
    contents: String,

    /// the current parsing line
    // line: u32,

    /// the current cursor column
    // column: u32,

    /// represents the imports in the file
    imports: HashMap<String, Parser>,
}

/// represents a parser struct this includes the file
impl Parser {
    fn new(filename: &str, contents: String) -> Result<Parser, ParserError> {
        let p = Parser {
            filename: filename.to_string(),
            contents: contents,
            imports: HashMap::new(),
            // line: 0,
            // column: 0
        };

        info!("created parser ");

        Ok(p)
    }

    #[allow(dead_code)]
    pub fn from_string(content: &str) -> Result<Parser, ParserError> {
        info!("creating string parser");
        Parser::new("<stdio>", content.to_string())
    }

    pub fn from_file(filename: &str) -> Result<Parser, ParserError> {
        info!("creating file parser for '{}'", filename);
        let file_contents = fs::read_to_string(filename);
        let contents = match file_contents {
            Ok(s) => s,
            _ => {
                error!("could not read the file '{}'", filename);
                return Err(ParserError::ReadSourceFile {
                    file: filename.to_string(),
                });
            }
        };
        Parser::new(filename, contents)
    }

    pub fn parse(&mut self) {
        info!("parsing: {}", self.filename);
        debug!("<contents>");
        debug!("{}", self.contents);
        debug!("<contents>");

        // so here we would parse the imports...
        info!("imports: ");
        for (k, _) in &self.imports {
            info!(" - {}", k)
        }

        let f = blockcomment(&self.contents);
        match f {
            _ => println!("todo"),
        }
        let f = comment(&self.contents);
        match f {
            _ => println!("todo"),
        }
    }
}
