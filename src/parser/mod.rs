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
use comments::{blockcomment, comment};

mod sourcepos;
use sourcepos::SourcePos;

mod ast;
mod identifier;
mod imports;
mod whitespace;

mod tokens;

use custom_error::custom_error;

use log::{debug, error, info};

use std::collections::HashMap;

custom_error! {pub ParserError
  ReadSourceFile{ file: String } = "Could not read the source file",
}

pub struct Parser<'a> {
    /// the filename that is being parser
    filename: String,

    /// the source code to be parser
    contents: SourcePos<'a>,

    /// represents the imports in the file
    imports: HashMap<String, Parser<'a>>,
}

/// represents a parser struct this includes the file
impl<'a> Parser<'a> {
    fn new(filename: &'a str, contents: &'a str) -> Result<Parser<'a>, ParserError> {
        let p = Parser {
            filename: filename.to_string(),
            contents: SourcePos::new(filename, contents),
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
        Parser::new("<stdio>", content)
    }

    // pub fn from_file(filename: &str) -> Result<Parser, ParserError> {
    //     info!("creating file parser for '{}'", filename);
    //     let file_contents = fs::read_to_string(filename);
    //     let contents = match file_contents {
    //         Ok(s) => s,
    //         _ => {
    //             error!("could not read the file '{}'", filename);
    //             return Err(ParserError::ReadSourceFile {
    //                 file: filename.to_string(),
    //             });
    //         }
    //     };
    //     Parser::new(filename, &contents.as_bytes())
    // }

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

        let f = blockcomment(self.contents);
        // match f {
        //     _ => println!("todo"),
        // }
        // let f = comment(&self.contents);
        // match f {
        //     _ => println!("todo"),
        // }
    }
}
