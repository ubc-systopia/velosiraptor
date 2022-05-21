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

//
use std::convert::TryInto;

// the used nom componets
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::{alpha1, alphanumeric1};
use nom::combinator::recognize;
use nom::multi::many0;
use nom::sequence::pair;

use crate::error::IResult;

use crate::sourcepos::SourcePos;
use crate::token::{Token, TokenContent};

/// parses a rust-like identifiers
pub fn identifier(input: SourcePos) -> IResult<SourcePos, Token> {
    // fist character must be an :alpha: or _
    let firstchar = alt((alpha1, tag("_")));
    // remaining characters must be :alphanumeric: or _
    let otherchar = alt((alphanumeric1, tag("_")));
    let (rem, ident) = recognize(pair(firstchar, many0(otherchar)))(input)?;

    match ident.as_str().try_into() {
        Ok(t) => Ok((rem, Token::new(TokenContent::Keyword(t), ident))),
        Err(x) => match x {
            "true" => Ok((rem, Token::new(TokenContent::BoolLiteral(true), ident))),
            "false" => Ok((rem, Token::new(TokenContent::BoolLiteral(false), ident))),
            x => Ok((
                rem,
                Token::new(TokenContent::Identifier(x.to_string()), ident),
            )),
        },
    }
}

#[cfg(test)]
use crate::token::Keyword;
#[cfg(test)]
use nom::Slice;

#[test]
fn identifier_test_alpha() {
    let sp = SourcePos::new("stdin", "foo");
    let rem = sp.slice(3..3);
    let ident = sp.slice(0..3);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(TokenContent::Identifier("foo".to_string()), ident)
        ))
    );

    let sp = SourcePos::new("stdin", "FoO");
    let rem = sp.slice(3..3);
    let ident = sp.slice(0..3);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(TokenContent::Identifier("FoO".to_string()), ident)
        ))
    );

    let sp = SourcePos::new(
        "stdin",
        "abcdefghijklmnopqrstuvwxzyABCDEFGHIJKLMNOPQRSTUVWXYZ",
    );
    let rem = sp.slice(52..52);
    let ident = sp.slice(0..52);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(
                TokenContent::Identifier(
                    "abcdefghijklmnopqrstuvwxzyABCDEFGHIJKLMNOPQRSTUVWXYZ".to_string()
                ),
                ident
            )
        ))
    );
}

#[test]
fn identifier_test_alnum() {
    let sp = SourcePos::new("stdin", "foo123bar");
    let rem = sp.slice(9..9);
    let ident = sp.slice(0..9);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(TokenContent::Identifier("foo123bar".to_string()), ident)
        ))
    );
}

#[test]
fn identifier_test_underscores() {
    let sp = SourcePos::new("stdin", "_foobar");
    let rem = sp.slice(7..7);
    let ident = sp.slice(0..7);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(TokenContent::Identifier("_foobar".to_string()), ident)
        ))
    );

    let sp = SourcePos::new("stdin", "_foo_bar_");
    let rem = sp.slice(9..9);
    let ident = sp.slice(0..9);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(TokenContent::Identifier("_foo_bar_".to_string()), ident)
        ))
    );
    let sp = SourcePos::new("stdin", "__foo__bar__");
    let rem = sp.slice(12..12);
    let ident = sp.slice(0..12);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(TokenContent::Identifier("__foo__bar__".to_string()), ident)
        ))
    );
}

#[test]
fn identifier_test_badbegin() {
    assert!(identifier(SourcePos::new("stdin", "1foo43")).is_err());
}

#[test]
fn identifier_test_badchars() {
    assert!(identifier(SourcePos::new("stdin", "@bar")).is_err());
    assert!(identifier(SourcePos::new("stdin", "#bar")).is_err());
}

#[test]
fn identifier_test_keywords() {
    let sp = SourcePos::new("stdin", "import");
    let rem = sp.slice(6..6);
    let ident = sp.slice(0..6);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(TokenContent::Keyword(Keyword::Import), ident)
        ))
    );

    let sp = SourcePos::new("stdin", "import2");
    let rem = sp.slice(7..7);
    let ident = sp.slice(0..7);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(TokenContent::Identifier("import2".to_string()), ident)
        ))
    );

    let sp = SourcePos::new("stdin", "unit");
    let rem = sp.slice(4..4);
    let ident = sp.slice(0..4);
    assert_eq!(
        identifier(sp),
        Ok((rem, Token::new(TokenContent::Keyword(Keyword::Unit), ident)))
    );

    let sp = SourcePos::new("stdin", "unit_");
    let rem = sp.slice(5..5);
    let ident = sp.slice(0..5);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(TokenContent::Identifier("unit_".to_string()), ident)
        ))
    );
}

#[test]
fn identifier_test_boolean() {
    let sp = SourcePos::new("stdin", "true");
    let rem = sp.slice(4..4);
    let ident = sp.slice(0..4);
    assert_eq!(
        identifier(sp),
        Ok((rem, Token::new(TokenContent::BoolLiteral(true), ident)))
    );

    let sp = SourcePos::new("stdin", "false");
    let rem = sp.slice(5..5);
    let ident = sp.slice(0..5);
    assert_eq!(
        identifier(sp),
        Ok((rem, Token::new(TokenContent::BoolLiteral(false), ident)))
    );
}
