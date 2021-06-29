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

//! parses a velosiraptor specification file

// the used nom componets
use nom::{
    character::complete::multispace0,
    multi::{many0, many1},
    sequence::{delimited, preceded},
    IResult,
};

// get the tokens
use super::SourcePos;

use super::ast::File;
use super::comments::parse_comments;
use super::imports::parse_import;
use super::unit::parse_unit;

///
pub fn parse_file(input: SourcePos) -> IResult<SourcePos, File> {
    // parsing imports, which may be proceeded by comments.
    let import_parser = many0(preceded(parse_comments, parse_import));

    // the file header is some white space, follwed by the imports
    let (input, imports) = match preceded(multispace0, import_parser)(input) {
        Ok((input, imports)) => (input, imports),
        Err(x) => {
            println!("error with parsing the imports");
            return Err(x);
        }
    };

    // the parser allows to have some comments, before every unit definition
    let unit_parser = many1(preceded(parse_comments, parse_unit));

    //
    let (input, units) = match delimited(multispace0, unit_parser, parse_comments)(input) {
        Ok((input, units)) => (input, units),
        Err(x) => {
            println!("error with parsing the units {}", input);
            return Err(x);
        }
    };

    Ok((input, File::new(input.filename.to_string(), imports, units)))
}
