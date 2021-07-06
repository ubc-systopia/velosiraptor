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

//! Parses numbers

extern crate lexical;

// the used nom components
use nom::{
    character::complete::{hex_digit1},
    IResult,
    Slice,
    branch::alt,
    combinator::recognize,
    bytes::complete::tag,
    //multi::many1,
};
use nom::sequence::pair;
use nom::character::complete::digit1;

// num library
//use std::num::from_str_radix;


use super::token::{Token, TokenContent};
use super::sourcepos::SourcePos;

/// Parses a rust-like number literal
pub fn number(input: SourcePos) -> IResult<SourcePos, Token> {

    let (rem, num) = match digit1(input) {
        Ok((remainder, num)) => (remainder, num),
        Err(x) => return Err(x),
    };

    // Create token
    println!("{}", num.as_str().to_string());
    let token = Token::new(TokenContent::IntLiteral(num.as_str().parse().unwrap()), num);

    Ok((rem, token))
}

// TODO: Add coverage for binary
pub fn prefix_number(input: SourcePos) -> IResult<SourcePos, Token> {

    // define option parsers
    let decimal = pair(tag("0d"), digit1);
    let hexadecimal = pair(tag("0x"), hex_digit1);
    let binary = pair(tag("0b"), many1(alt((tag("0", tag("1")))));

    let (rem, num) = match recognize(alt((decimal, hexadecimal)))(input) {
        Ok((remainder, num)) => (remainder, num),
        Err(x) => return Err(x),
    };

    // Create token
    let value = &num.as_str();
    println!("{}", value);
    let token = Token::new(TokenContent::IntLiteral(parse_number_with_prefix(value).unwrap()), num);

    Ok((rem, token))
}

fn parse_number_with_prefix(num: &str) -> Option<u64> {
    let radix = match &num[1..1] {
        "d" => 10,
        "x" => 16,
        "b" => 2,
        _   => return None,
    };

    u64::from_str_radix(&str[2..], radix)
}

#[cfg(test)]

#[test]
fn decimal_test() {
    let sp = SourcePos::new("stdin", "12312");
    let rem = sp.slice(5..5);
    let num = sp.slice(0..5);
    assert_eq!(
        number(sp),
        Ok((
            rem,
            Token::new(TokenContent::IntLiteral(12312), num)
        ))
    );

    let sp = SourcePos::new("stdin", "0d12312");
    let rem = sp.slice(7..7);
    let num = sp.slice(0..7);
    assert_eq!(
        prefix_number(sp),
        Ok((
            rem,
            Token::new(TokenContent::IntLiteral(12312), num)
        ))
    );
}

#[test]
fn hexadecimal_test() {
    let sp = SourcePos::new("stdin", "0xABCD");
    let rem = sp.slice(4..4);
    let num = sp.slice(0..4);
    assert_eq!(
        prefix_number(sp),
        Ok((
            rem,
            Token::new(TokenContent::IntLiteral(0xABCD), num)
        ))
    );
}



