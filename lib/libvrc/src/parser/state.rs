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

//! State definition parsing

// lexer, parser terminals and ast
use crate::ast::ast::{Field, State};
use crate::lexer::token::{TokenStream};
use crate::parser::field::field;
use crate::parser::terminals::{ident, kw_state, kw_register, kw_memory, eq, comma, lparen, rparen, lbrace, rbrace, semicolon};
//use crate::parser::field::field;


use nom::multi::separated_list0;
// the used nom componets
use nom::{
    error::ErrorKind, 
    error_position, 
    Err, 
    IResult,
};
use nom::sequence::{delimited};
use nom::branch::alt;

/// parses and consumes the [State] of a unit
pub fn state(input: TokenStream) -> IResult<TokenStream, State> {
    // try to match the state keyword, if there is no match, return.
    let (i1, _)= kw_state(input)?;
    // Er now 
    delimited(eq, alt((register_state, memory_state)), semicolon)(i1)
}

fn register_state(input: TokenStream) -> IResult<TokenStream, State> {

    let pos = input.input_sourcepos();

    let (i1, _) = kw_register(input)?;
    let (i2, fields) = fields_parser(i1)?;

    Ok((i2, State::RegisterState{ fields, pos }))
    //Ok((i1, State::RegisterState{ fields, pos }))
}

fn memory_state(input: TokenStream) -> IResult<TokenStream, State> {

    let pos = input.input_sourcepos();

    let (i1, _) = kw_memory(input)?;
    let (i2, bases) = argument_parser(i1)?;
    let (i3, fields) = fields_parser(i2)?;

    Ok((i3, State::MemoryState{ bases, fields, pos }))
}

pub fn argument_parser(input: TokenStream) -> IResult<TokenStream, Vec<String>> {
    match delimited(lparen, separated_list0(comma, ident), rparen)(input.clone()) {
        Ok((i1, arguments)) => Ok((i1, arguments)),
        Err(e) => {
            let (i, k) = match e {
                Err::Error(e) => (e.input, e.code),
                Err::Failure(e) => (e.input, e.code),
                Err::Incomplete(_) => (input, ErrorKind::Eof),
            };
            return Err(Err::Failure(error_position!(i, k)));
        }
    }
}

pub fn fields_parser(input: TokenStream) -> IResult<TokenStream, Vec<Field>> {
    match delimited(lbrace, separated_list0(comma, field), rbrace)(input.clone()) {
        Ok((i1, fields)) => Ok((i1, fields)),
        Err(e) => {
            let (i, k) = match e {
                Err::Error(e) => (e.input, e.code),
                Err::Failure(e) => (e.input, e.code),
                Err::Incomplete(_) => (input, ErrorKind::Eof),
            };
            Err(Err::Failure(error_position!(i, k)))
        }
    }
}

// parses and consumes an import statement (`import foo;`) and any following whitespaces
/* pub fn state(input: SourcePos) -> IResult<SourcePos, State> {
    // record the current position
    let pos = input.get_pos();

    let (input, _) = kw_state(input)?;

    // get the type of the state
    let (input, statetype) = match alt((tag("Memory"), tag("Register")))(input) {
        Ok((input, statetype)) => (input, statetype),
        Err(x) => return Err(x),
    };

    // the entries are a comma separeted list entries, where each entry may have some comments before
    let baseslist = separated_list1(comma, parse_identifier);

    // the baseslist is enclosed in parenthesis
    let header = preceded(multispace0, delimited(lparen, baseslist, rparen));

    // parse the header of the state, and at least one field
    let (input, bases, fields) = match tuple((header, many1(parse_field)))(input) {
        Ok((input, (bases, fields))) => (input, bases, fields),
        Err(x) => return Err(x),
    };

    if statetype.as_slice() == "Memory" {
        Ok((input, State::MemoryState { bases, fields, pos }))
    } else {
        Ok((input, State::RegisterState { bases, fields, pos }))
    }
} */

#[test]
fn parse_field_test() {
    assert_eq!(
        parse_field(SourcePos::new("stdin", "foo [ bar, 0, 2 ] { 1 2 foobar };")),
        Ok((
            SourcePos::new_at("stdin", "", 33, 1, 34),
            StateField {
                name: "foo".to_string(),
                base: "bar".to_string(),
                offset: 0,
                length: 2,
                bitmap: vec![BitMapEntry {
                    start: 1,
                    end: 2,
                    name: "foobar".to_string(),
                    pos: (1, 21)
                }],
                pos: (1, 1)
            },
        ))
    );

    assert_eq!(
        parse_field(SourcePos::new("stdin", "foo[bar,0,2] {1 2 foobar};")),
        Ok((
            SourcePos::new_at("stdin", "", 26, 1, 27),
            StateField {
                name: "foo".to_string(),
                base: "bar".to_string(),
                offset: 0,
                length: 2,
                bitmap: vec![BitMapEntry {
                    start: 1,
                    end: 2,
                    name: "foobar".to_string(),
                    pos: (1, 15)
                }],
                pos: (1, 1)
            },
        ))
    );

    assert_eq!(
        parse_field(SourcePos::new(
            "stdin",
            "foo[bar,0,2] {// some comment \n 1 2 foobar\n};"
        )),
        Ok((
            SourcePos::new_at("stdin", "", 45, 3, 3),
            StateField {
                name: "foo".to_string(),
                base: "bar".to_string(),
                offset: 0,
                length: 2,
                bitmap: vec![BitMapEntry {
                    start: 1,
                    end: 2,
                    name: "foobar".to_string(),
                    pos: (2, 2)
                }],
                pos: (1, 1)
            },
        ))
    );

    // multiple entries in the list
    assert!(parse_field(SourcePos::new(
        "stdin",
        "foo [ bar, 0, 2 ] { 1 2 foobar, 1 2 foobar };"
    ))
    .is_ok());
    assert!(parse_field(SourcePos::new(
        "stdin",
        "foo [ bar, 0, 2 ] { 1 2 foobar,\n 1 2 foobar\n };"
    ))
    .is_ok());
    assert!(parse_field(SourcePos::new(
        "stdin",
        "foo [ bar, 0, 2 ] { 1 2 foobar\n,\n 1 2 foobar\n };"
    ))
    .is_ok());

    // adding comments to the entries
    assert!(parse_field(SourcePos::new(
        "stdin",
        "foo [ bar, 0, 2 ] { // comment 1\n1 2 foobar,\n// comment 2\n 1 2 foobar\n };"
    ))
    .is_ok());
    assert!(parse_field(SourcePos::new(
        "stdin",
        "foo [ bar, 0, 2 ] { // comment 1\n1 2 foobar };"
    ))
    .is_ok());
    // no comments after the entry
    assert!(parse_field(SourcePos::new(
        "stdin",
        "foo [ bar, 0, 2 ] { 1 2 foobar// no comment here\n };"
    ))
    .is_err());
    assert!(parse_field(SourcePos::new(
        "stdin",
        "foo [ bar, 0, 2 ] { 1 2 foobar// no comment here\n, 1 2 foobar\n };"
    ))
    .is_err());
}
