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

use std::collections::HashMap;

/// the file extension for velosiraptor files
const FILE_EXTENSION: &str = ".vrs";

custom_error! {pub ParserError
  ReadSourceFile{ file: String } = "Could not read the source file",
  ParsingError = "The parser returned an error",
  ParserNotFinished = "There was unexpected chunk at the ned of input",
  SyntaxError = "Attempt to parse resulted in a syntax error.",
  NoParseTree = "There was not parse tree",
  ResolveImports = "There was an error when resolving the imports"
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
    fn new(filename: String, filecontents: String) -> Result<Parser, ParserError> {
        let p = Parser {
            filename,
            filecontents,
            imports: HashMap::new(),
            parsetree: None,
        };

        log::info!("created parser ");
        Ok(p)
    }

    #[allow(dead_code)]
    pub fn from_string(contents: String) -> Result<Parser, ParserError> {
        log::info!("creating string parser");
        Parser::new("<stdio>".to_string(), contents)
    }

    pub fn from_file(filename: String) -> Result<Parser, ParserError> {
        log::info!("creating file parser for '{}'", filename);
        let file_contents = fs::read_to_string(&filename);
        let contents = match file_contents {
            Ok(s) => s,
            _ => {
                log::error!("could not read the file '{}'", filename);
                return Err(ParserError::ReadSourceFile { file: filename });
            }
        };
        Parser::new(filename, contents)
    }

    pub fn parse(&mut self) -> Result<(), ParserError> {
        log::info!("parsing: {}", self.filename);
        log::debug!("<contents>");
        log::debug!("{}", &self.filecontents);
        log::debug!("<contents>");

        // create the source position struct
        let sp = SourcePos::new(&self.filename, &self.filecontents);

        // try to parse the file
        let (remainder, ast) = match parse_file(sp) {
            Ok((input, ast)) => (input, ast),
            Err(_) => return Err(ParserError::ParsingError),
        };

        // should  not have any chunk at the end of the file
        if !remainder.is_empty() {
            return Err(ParserError::ParserNotFinished);
        }

        // save the parse tree in the structure
        self.parsetree = Some(ast);

        log::debug!("<parsetree>");
        log::debug!("{}", self.parsetree.as_ref().unwrap());
        log::debug!("<parsetree>");

        Ok(())
    }

    fn resolve_imports_recurively(
        &mut self,
        parsers: &mut HashMap<String, bool>,
    ) -> Result<(), ParserError> {
        let parsetree = self.parsetree.as_ref().unwrap();
        for import in &parsetree.imports {
            // todo: adjust path to be relative for this
            let mut filename = import.filename.to_owned();
            filename.push_str(FILE_EXTENSION);

            if parsers.contains_key(&filename) {
                // this may be a bit too aggressive...
                log::error!("potential circular import dependency detected! aborting for now");
                return Err(ParserError::ResolveImports);
            }

            let mut import_parser = match Parser::from_file(filename.to_string()) {
                Ok(p) => p,
                Err(e) => {
                    log::error!("could not resolve import {}", &filename);
                    return Err(e);
                }
            };
            let err = import_parser.parse();
            if err.is_err() {
                return err;
            }

            // add the parser to the seen elements
            parsers.insert(filename.to_string(), true);

            let err = import_parser.resolve_imports_recurively(parsers);
            if err.is_err() {
                return err;
            }

            self.imports.insert(filename, import_parser);
        }
        Ok(())
    }

    pub fn resolve_imports(&mut self) -> Result<(), ParserError> {
        log::info!("resolving imports...");
        if self.parsetree.is_none() {
            log::warn!("there was no parse tree, parse first!");
            return Err(ParserError::NoParseTree);
        }

        // create a hashmap with the currently parsed files...
        let mut parsers: HashMap<String, bool> = HashMap::new();
        parsers.insert(self.filename.to_string(), true);

        // recursively resolve the imports
        self.resolve_imports_recurively(&mut parsers)
    }
}
