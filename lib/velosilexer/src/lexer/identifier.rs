// VelosiLexer -- Identifier Lexing
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

// used standard library functionality
use std::convert::TryInto;

// used exernal dependencies
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::{alpha1, alphanumeric1};
use nom::combinator::recognize;
use nom::multi::many0;
use nom::sequence::pair;

use crate::error::IResult;

use crate::{SrcSpan, Token, VelosiToken, VelosiTokenKind};

/// parses a rust-like identifiers
pub fn identifier(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
    // fist character must be an :alpha: or _
    let firstchar = alt((alpha1, tag("_")));
    // remaining characters must be :alphanumeric: or _
    let otherchar = alt((alphanumeric1, tag("_")));
    let (rem, ident) = recognize(pair(firstchar, many0(otherchar)))(input)?;

    match ident.as_str().try_into() {
        Ok(t) => Ok((rem, Token::new(VelosiTokenKind::Keyword(t), ident))),
        Err(x) => match x {
            "true" => Ok((rem, Token::new(VelosiTokenKind::BoolLiteral(true), ident))),
            "false" => Ok((rem, Token::new(VelosiTokenKind::BoolLiteral(false), ident))),
            x => Ok((
                rem,
                Token::new(VelosiTokenKind::Identifier(x.to_string()), ident),
            )),
        },
    }
}

#[cfg(test)]
use crate::VelosiKeyword;
#[cfg(test)]
use nom::Slice;

#[test]
fn identifier_test_alpha() {
    let sp = SrcSpan::new("foo".to_string());
    let rem = sp.slice(3..3);
    let ident = sp.slice(0..3);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::Identifier("foo".to_string()), ident)
        ))
    );

    let sp = SrcSpan::new("FoO".to_string());
    let rem = sp.slice(3..3);
    let ident = sp.slice(0..3);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::Identifier("FoO".to_string()), ident)
        ))
    );

    let sp = SrcSpan::new("abcdefghijklmnopqrstuvwxzyABCDEFGHIJKLMNOPQRSTUVWXYZ".to_string());
    let rem = sp.slice(52..52);
    let ident = sp.slice(0..52);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(
                VelosiTokenKind::Identifier(
                    "abcdefghijklmnopqrstuvwxzyABCDEFGHIJKLMNOPQRSTUVWXYZ".to_string()
                ),
                ident
            )
        ))
    );
}

#[test]
fn identifier_test_alnum() {
    let sp = SrcSpan::new("foo123bar".to_string());
    let rem = sp.slice(9..9);
    let ident = sp.slice(0..9);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::Identifier("foo123bar".to_string()), ident)
        ))
    );
}

#[test]
fn identifier_test_underscores() {
    let sp = SrcSpan::new("_foobar".to_string());
    let rem = sp.slice(7..7);
    let ident = sp.slice(0..7);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::Identifier("_foobar".to_string()), ident)
        ))
    );

    let sp = SrcSpan::new("_foo_bar_".to_string());
    let rem = sp.slice(9..9);
    let ident = sp.slice(0..9);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::Identifier("_foo_bar_".to_string()), ident)
        ))
    );
    let sp = SrcSpan::new("__foo__bar__".to_string());
    let rem = sp.slice(12..12);
    let ident = sp.slice(0..12);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(
                VelosiTokenKind::Identifier("__foo__bar__".to_string()),
                ident
            )
        ))
    );
}

#[test]
fn identifier_test_badbegin() {
    assert!(identifier(SrcSpan::new("1foo43".to_string())).is_err());
}

#[test]
fn identifier_test_badchars() {
    assert!(identifier(SrcSpan::new("@bar".to_string())).is_err());
    assert!(identifier(SrcSpan::new("#bar".to_string())).is_err());
}

#[test]
fn identifier_test_keywords() {
    let sp = SrcSpan::new("import".to_string());
    let rem = sp.slice(6..6);
    let ident = sp.slice(0..6);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::Keyword(VelosiKeyword::Import), ident)
        ))
    );

    let sp = SrcSpan::new("import2".to_string());
    let rem = sp.slice(7..7);
    let ident = sp.slice(0..7);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::Identifier("import2".to_string()), ident)
        ))
    );

    let sp = SrcSpan::new("unit".to_string());
    let rem = sp.slice(4..4);
    let ident = sp.slice(0..4);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::Keyword(VelosiKeyword::Unit), ident)
        ))
    );

    let sp = SrcSpan::new("unit_".to_string());
    let rem = sp.slice(5..5);
    let ident = sp.slice(0..5);
    assert_eq!(
        identifier(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::Identifier("unit_".to_string()), ident)
        ))
    );
}

#[test]
fn identifier_test_boolean() {
    let sp = SrcSpan::new("true".to_string());
    let rem = sp.slice(4..4);
    let ident = sp.slice(0..4);
    assert_eq!(
        identifier(sp),
        Ok((rem, Token::new(VelosiTokenKind::BoolLiteral(true), ident)))
    );

    let sp = SrcSpan::new("false".to_string());
    let rem = sp.slice(5..5);
    let ident = sp.slice(0..5);
    assert_eq!(
        identifier(sp),
        Ok((rem, Token::new(VelosiTokenKind::BoolLiteral(false), ident)))
    );
}
