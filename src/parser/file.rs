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
    branch::alt,
    bytes::complete::tag,
    character::complete::multispace0,
    multi::{many0, many_till},
    sequence::{pair, preceded},
    IResult,
};

// get the tokens
use super::SourcePos;

use super::ast::Ast;
use super::comments::parse_comments;
use super::imports::parse_import;

///
pub fn parse_file(input: SourcePos) -> IResult<SourcePos, Ast> {
    // a parser for matching white space and comments
    //let wscom = many0(alt((multispace1, blockcomment, comment)));

    // parsing imports, which may be proceeded by comments.
    let import_parser = many0(preceded(parse_comments, parse_import));

    // the file header is some white space, follwed by the imports
    let mut parse_header = preceded(multispace0, import_parser);

    // parse the units
    // let parse_units = many0(preceded(parse_comments, import));

    // let's parse the file header
    let (input, imports) = parse_header(input)?;

    println!("step 2");
    println!("{}", input);
    for i in imports {
        println!("{}", i);
    }

    Ok((
        input,
        Ast::File {
            name: "fooo".to_string(),
            imports: Box::new(Ast::None),
            units: Box::new(Ast::Unit {
                name: "bar".to_string(),
                pos: (1, 1),
            }),
        },
    ))
}
