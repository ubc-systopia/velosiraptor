// VelosiLexer -- Identifier Lexing
//
//
// MIT License
//
// Copyright (c) 2021-2023 Systopia Lab, Computer Science, University of British Columbia
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

//! VelosiLexer - Identifyer and Keyword Parsing

// used standard library functionality
use std::convert::TryInto;

// used external dependencies
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1},
    combinator::recognize,
    multi::many0,
    sequence::pair,
};
use tokstream::{SrcSpan, Tok};

// used crate dependencies
use crate::error::IResult;
use crate::{VelosiToken, VelosiTokenKind};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Identifyer parser
////////////////////////////////////////////////////////////////////////////////////////////////////

/// parses a rust-like identifiers and recognizes keywords
///
/// This parses a string of characters and recognizes keywords as defined in [crate::VelosiKeyword].
///
/// # Arguments
///
/// * `input` - the input source span to be lexed
///
/// # Returns
///
/// Returns a tuple of the remaining input and the parsed identifier or keyword token on success.
/// Otherwise, the an [crate::error::VelosiLexerErr] error is returned.
///
/// # Grammar
///
/// `IDENTIFIER := [A-Za-z_][A-Za-z0-9_]*`
///
pub fn identifier_or_keyword(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
    // fist character must be an :alpha: or _
    let firstchar = alt((alpha1, tag("_")));
    // remaining characters must be :alphanumeric: or _
    let otherchar = alt((alphanumeric1, tag("_")));
    let (rem, ident) = recognize(pair(firstchar, many0(otherchar)))(input)?;

    // we try to match the keywords and if we succeed we return the keyword token, otherwise
    // we return the identifier
    match ident.as_str().try_into() {
        Ok(t) => Ok((rem, Tok::new(VelosiTokenKind::Keyword(t), ident))),
        Err(x) => match x {
            "true" => Ok((rem, Tok::new(VelosiTokenKind::BoolLiteral(true), ident))),
            "false" => Ok((rem, Tok::new(VelosiTokenKind::BoolLiteral(false), ident))),
            x => Ok((
                rem,
                Tok::new(VelosiTokenKind::Identifier(x.to_string()), ident),
            )),
        },
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////////////////////////////

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
        identifier_or_keyword(sp),
        Ok((
            rem,
            VelosiToken::new(VelosiTokenKind::Identifier("foo".to_string()), ident)
        ))
    );

    let sp = SrcSpan::new("FoO".to_string());
    let rem = sp.slice(3..3);
    let ident = sp.slice(0..3);
    assert_eq!(
        identifier_or_keyword(sp),
        Ok((
            rem,
            VelosiToken::new(VelosiTokenKind::Identifier("FoO".to_string()), ident)
        ))
    );

    let sp = SrcSpan::new("abcdefghijklmnopqrstuvwxzyABCDEFGHIJKLMNOPQRSTUVWXYZ".to_string());
    let rem = sp.slice(52..52);
    let ident = sp.slice(0..52);
    assert_eq!(
        identifier_or_keyword(sp),
        Ok((
            rem,
            VelosiToken::new(
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
        identifier_or_keyword(sp),
        Ok((
            rem,
            VelosiToken::new(VelosiTokenKind::Identifier("foo123bar".to_string()), ident)
        ))
    );
}

#[test]
fn identifier_test_underscores() {
    let sp = SrcSpan::new("_foobar".to_string());
    let rem = sp.slice(7..7);
    let ident = sp.slice(0..7);
    assert_eq!(
        identifier_or_keyword(sp),
        Ok((
            rem,
            VelosiToken::new(VelosiTokenKind::Identifier("_foobar".to_string()), ident)
        ))
    );

    let sp = SrcSpan::new("_foo_bar_".to_string());
    let rem = sp.slice(9..9);
    let ident = sp.slice(0..9);
    assert_eq!(
        identifier_or_keyword(sp),
        Ok((
            rem,
            VelosiToken::new(VelosiTokenKind::Identifier("_foo_bar_".to_string()), ident)
        ))
    );
    let sp = SrcSpan::new("__foo__bar__".to_string());
    let rem = sp.slice(12..12);
    let ident = sp.slice(0..12);
    assert_eq!(
        identifier_or_keyword(sp),
        Ok((
            rem,
            VelosiToken::new(
                VelosiTokenKind::Identifier("__foo__bar__".to_string()),
                ident
            )
        ))
    );
}

#[test]
fn identifier_test_badbegin() {
    assert!(identifier_or_keyword(SrcSpan::new("1foo43".to_string())).is_err());
}

#[test]
fn identifier_test_badchars() {
    assert!(identifier_or_keyword(SrcSpan::new("@bar".to_string())).is_err());
    assert!(identifier_or_keyword(SrcSpan::new("#bar".to_string())).is_err());
}

#[test]
fn identifier_test_keywords() {
    let sp = SrcSpan::new("import".to_string());
    let rem = sp.slice(6..6);
    let ident = sp.slice(0..6);
    assert_eq!(
        identifier_or_keyword(sp),
        Ok((
            rem,
            VelosiToken::new(VelosiTokenKind::Keyword(VelosiKeyword::Import), ident)
        ))
    );

    let sp = SrcSpan::new("import2".to_string());
    let rem = sp.slice(7..7);
    let ident = sp.slice(0..7);
    assert_eq!(
        identifier_or_keyword(sp),
        Ok((
            rem,
            VelosiToken::new(VelosiTokenKind::Identifier("import2".to_string()), ident)
        ))
    );

    let sp = SrcSpan::new("unit_".to_string());
    let rem = sp.slice(5..5);
    let ident = sp.slice(0..5);
    assert_eq!(
        identifier_or_keyword(sp),
        Ok((
            rem,
            VelosiToken::new(VelosiTokenKind::Identifier("unit_".to_string()), ident)
        ))
    );
}

#[test]
fn identifier_test_boolean() {
    let sp = SrcSpan::new("true".to_string());
    let rem = sp.slice(4..4);
    let ident = sp.slice(0..4);
    assert_eq!(
        identifier_or_keyword(sp),
        Ok((
            rem,
            VelosiToken::new(VelosiTokenKind::BoolLiteral(true), ident)
        ))
    );

    let sp = SrcSpan::new("false".to_string());
    let rem = sp.slice(5..5);
    let ident = sp.slice(0..5);
    assert_eq!(
        identifier_or_keyword(sp),
        Ok((
            rem,
            VelosiToken::new(VelosiTokenKind::BoolLiteral(false), ident)
        ))
    );
}
