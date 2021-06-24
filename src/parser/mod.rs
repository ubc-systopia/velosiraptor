// Velosiraptor Compiler
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

mod sourcepos;
use sourcepos::SourcePos;

mod file;
use file::parse_file;

mod ast;
mod identifier;
mod imports;
mod state;
mod tokens;
mod unit;

use custom_error::custom_error;

use log::{debug, error, info};

use std::collections::HashMap;

custom_error! {pub ParserError
  ReadSourceFile{ file: String } = "Could not read the source file",
}

pub struct Parser {
    /// the filename that is being parser
    filename: String,

    /// the contents of this file
    filecontents: String,

    /// represents the imports in the file
    imports: HashMap<String, Parser>,

    parsetree: Option<ast::File>,
}

/// represents a parser struct this includes the file
impl Parser {
    fn new(filename: String, contents: String) -> Result<Parser, ParserError> {
        let p = Parser {
            filename: filename.to_string(),
            filecontents: contents,
            imports: HashMap::new(),
            parsetree: None,
        };

        info!("created parser ");
        Ok(p)
    }

    #[allow(dead_code)]
    pub fn from_string(contents: String) -> Result<Parser, ParserError> {
        info!("creating string parser");
        Parser::new("<stdio>".to_string(), contents)
    }

    pub fn from_file(filename: String) -> Result<Parser, ParserError> {
        info!("creating file parser for '{}'", filename);
        let file_contents = fs::read_to_string(&filename);
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
        debug!("{}", &self.filecontents);
        debug!("<contents>");

        let sp = SourcePos::new(&self.filename, &self.filecontents);
        let (rem, ast) = parse_file(sp).unwrap();

        println!("{}", ast);
        println!("{}", rem);
    }
}
