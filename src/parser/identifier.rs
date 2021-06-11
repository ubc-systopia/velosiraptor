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

//! Parses identifiers

// the used nom componets
use nom::{
    character::complete::{alpha1, alphanumeric1},
    combinator::peek,
    IResult,
};

#[cfg(test)]
use nom::{
    error::{Error, ErrorKind},
    Err,
};

// get the tokens
use super::SourcePos;

/// parses an identifier from the input stream
pub fn parse_identifier(input: SourcePos) -> IResult<SourcePos, String> {
    // must start with with an alpha character
    let parse = match peek(alpha1)(input) {
        // return the alpha numeric identifier
        Ok(_) => alphanumeric1(input),
        // otherwise pass the error
        Err(x) => Err(x),
    };

    match parse {
        // parsing succeeded, construct the identifier result
        Ok((input, ident)) => Ok((input, ident.to_string())),
        // otherwise pass the error
        Err(x) => Err(x),
    }
}

#[test]
fn parse_identifier_test() {
    assert_eq!(
        parse_identifier(SourcePos::new("stdin", "foo")),
        Ok((SourcePos::new_at("stdin", "", 3, 1, 4), "foo".to_string()))
    );
}

#[test]
fn parse_identifier_test_alnum() {
    assert_eq!(
        parse_identifier(SourcePos::new("stdin", "foo43")),
        Ok((SourcePos::new_at("stdin", "", 5, 1, 6), "foo43".to_string(),))
    );
}

#[test]
fn parse_identifier_test_badbegin() {
    assert_eq!(
        parse_identifier(SourcePos::new("stdin", "1foo43")),
        Err(Err::Error(Error {
            input: SourcePos::new("stdin", "1foo43"),
            code: ErrorKind::Alpha
        }))
    );
}
