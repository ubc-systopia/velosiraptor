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

// the used nom componets
use nom::{
    branch::alt,
    bytes::complete::{is_a, tag},
    character::complete::{alphanumeric1, digit1, hex_digit1, oct_digit1},
    combinator::recognize,
    multi::many0,
    sequence::pair,
    Err, InputLength, Slice,
};

use crate::error::{IResult, VrsError};
use crate::sourcepos::SourcePos;
use crate::token::{Token, TokenContent};

fn base10(input: SourcePos) -> IResult<SourcePos, Token> {
    // match a digit followed by alphanumeric characters and the `_`
    // this is needed to recognize patterns of: 1234asdf
    let otherchar = alt((alphanumeric1, tag("_")));
    let (rem, numsp) = recognize(pair(digit1, many0(otherchar)))(input)?;

    // allow groups of digits 1234_5678
    let otherdigits = alt((digit1, tag("_")));

    // parse the numsp again, with restricted tokens
    let (rem1, _) = recognize(pair(digit1, many0(otherdigits)))(numsp.clone())?;

    // if it's not empty there will be some junk at the end of the number
    if !rem1.is_empty() {
        let err = VrsError::new_err(
            rem1,
            String::from("unsupported digit in number."),
            Some(String::from("remove excess characters")),
        );
        return Err(Err::Failure(err));
    }

    // now convert the string to to a number
    let numstr = String::from(numsp.as_str()).replace('_', "");
    let num = match numstr.parse::<u64>() {
        Ok(i) => i,
        Err(_) => {
            let err = VrsError::new_err(rem1, String::from("number exceeds available bits"), None);
            return Err(Err::Failure(err));
        }
    };
    Ok((rem, Token::new(TokenContent::IntLiteral(num), numsp)))
}

macro_rules! namedbase (
    ($name:ident, $radix:expr, $tag:expr, $pattern:expr) => (
        fn $name(input: SourcePos) -> IResult<SourcePos, Token> {
            // check if it's the right tag `0x`, otherwise return
            let prefix = tag($tag);
            let (i1, _) = prefix(input.clone())?;

            // match alphanumeric groups separated by `_`
            let otherchar = alt((alphanumeric1, tag("_")));
            let (rem, numsp) = recognize(pair(alphanumeric1, many0(otherchar)))(i1.clone())?;

            // allow groups of digits 1234_abcd
            let otherdigits = alt(($pattern, tag("_")));

            // parse the numsp again, with restricted tokens
            let (rem1, _) = recognize(pair($pattern, many0(otherdigits)))(numsp.clone())?;

            // if it's not empty there will be some junk at the end of the number
            if ! rem1.is_empty() {
                let err = VrsError::new_err(rem1,
                    String::from("unsupported digit in number."),
                    Some(String::from("remove excess characters")));
                return Err(Err::Failure(err));
            }

            // now convert the string to to a number
            let numstr = String::from(numsp.as_str()).replace("_", "");
            match u64::from_str_radix(&numstr, $radix) {
                Ok(i) => Ok((rem, Token::new(TokenContent::IntLiteral(i), input.slice(0..numsp.input_len() + 2)))),
                Err(_) => {
                    let err = VrsError::new_err(rem1,
                        String::from("number exceeds available bits"),
                        None);
                    Err(Err::Failure(err))
                }
            }
        }
    )
);

namedbase!(base16, 16, "0x", hex_digit1);
namedbase!(base8, 8, "0o", oct_digit1);
namedbase!(base2, 2, "0b", is_a("01"));

/// parses a rust-like identifiers
pub fn number(input: SourcePos) -> IResult<SourcePos, Token> {
    alt((base16, base8, base2, base10))(input)
}

#[test]
fn decimal_test() {
    let sp = SourcePos::new("stdin", "12312");
    let rem = sp.slice(5..5);
    let num = sp.slice(0..5);
    assert_eq!(
        number(sp),
        Ok((rem, Token::new(TokenContent::IntLiteral(12312), num)))
    );

    let sp = SourcePos::new("stdin", "12312213489654");
    let rem = sp.slice(14..14);
    let num = sp.slice(0..14);
    assert_eq!(
        number(sp),
        Ok((
            rem,
            Token::new(TokenContent::IntLiteral(12312213489654), num)
        ))
    );
}

#[test]
fn hexadecimal_test() {
    let sp = SourcePos::new("stdin", "0xABCD");
    let rem = sp.slice(6..6);
    let num = sp.slice(0..6);
    assert_eq!(
        number(sp),
        Ok((rem, Token::new(TokenContent::IntLiteral(0xABCD), num)))
    );

    let sp = SourcePos::new("stdin", "0xabcd");
    let rem = sp.slice(6..6);
    let num = sp.slice(0..6);
    assert_eq!(
        number(sp),
        Ok((rem, Token::new(TokenContent::IntLiteral(0xABCD), num)))
    );
}

#[test]
fn octal_test() {
    let sp = SourcePos::new("stdin", "0o1234");
    let rem = sp.slice(6..6);
    let num = sp.slice(0..6);
    assert_eq!(
        number(sp),
        Ok((rem, Token::new(TokenContent::IntLiteral(0o1234), num)))
    );
}

#[test]
fn binary_test() {
    let sp = SourcePos::new("stdin", "0b1000");
    let rem = sp.slice(6..6);
    let num = sp.slice(0..6);
    assert_eq!(
        number(sp),
        Ok((rem, Token::new(TokenContent::IntLiteral(0b1000), num)))
    );
}

#[test]
fn separator_test() {
    let sp = SourcePos::new("stdin", "0b1111_0000");
    let rem = sp.slice(11..11);
    let num = sp.slice(0..11);
    assert_eq!(
        number(sp),
        Ok((rem, Token::new(TokenContent::IntLiteral(0b11110000), num)))
    );

    let sp = SourcePos::new("stdin", "0o4567_1234");
    let rem = sp.slice(11..11);
    let num = sp.slice(0..11);
    assert_eq!(
        number(sp),
        Ok((rem, Token::new(TokenContent::IntLiteral(0o45671234), num)))
    );

    let sp = SourcePos::new("stdin", "0xabcd_1234");
    let rem = sp.slice(11..11);
    let num = sp.slice(0..11);
    assert_eq!(
        number(sp),
        Ok((rem, Token::new(TokenContent::IntLiteral(0xabcd1234), num)))
    );

    let sp = SourcePos::new("stdin", "1_000_000");
    let rem = sp.slice(9..9);
    let num = sp.slice(0..9);
    assert_eq!(
        number(sp),
        Ok((rem, Token::new(TokenContent::IntLiteral(1000000), num)))
    );

    let sp = SourcePos::new("stdin", "0o11223344 asdf");
    assert!(number(sp).is_ok());

    let sp = SourcePos::new("stdin", "0b11001100 asdf");
    assert!(number(sp).is_ok());
}

#[test]
fn not_a_number() {
    let sp = SourcePos::new("stdin", "12354asdf");
    assert!(number(sp).is_err());

    let sp = SourcePos::new("stdin", "0x1234oiweu");
    assert!(number(sp).is_err());

    let sp = SourcePos::new("stdin", "0o123lajks");
    assert!(number(sp).is_err());

    let sp = SourcePos::new("stdin", "0b11123");
    assert!(number(sp).is_err());

    let sp = SourcePos::new("stdin", "0b");
    assert!(number(sp).is_err());

    let sp = SourcePos::new("stdin", "0x");
    assert!(number(sp).is_err());

    let sp = SourcePos::new("stdin", "0o");
    assert!(number(sp).is_err());
}

#[test]
fn out_of_range_test() {
    let sp = SourcePos::new("stdin", "0x10000000000000000");
    assert!(number(sp).is_err());
}
