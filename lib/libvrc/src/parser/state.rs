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
use crate::lexer::token::TokenStream;
use crate::parser::ast::State;
use crate::parser::terminals::{ident, import_keyword, semicolon};

// the used nom componets
use nom::error::ErrorKind;
use nom::sequence::terminated;
use nom::{error_position, Err, IResult};

// the used nom componets
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{digit1, multispace0, multispace1},
    multi::{many1, separated_list1},
    sequence::{delimited, preceded, terminated, tuple},
    IResult,
};

// get the tokens
use super::comments::parse_comments;
use super::identifier::parse_identifier;
use super::tokens::{comma, lbrace, lbrack, lparen, rbrace, rbrack, rparen, semicolon};
use super::SourcePos;

use super::ast::{BitMapEntry, State, StateField};

/// parses and consumes an import statement (`import foo;`) and any following whitespaces
pub fn parse_state(input: SourcePos) -> IResult<SourcePos, State> {
    // record the current position
    let pos = input.get_pos();

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
}


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
