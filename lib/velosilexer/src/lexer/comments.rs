// Velosilexer -- Comment Lexing
//
//
// MIT License
//
// Copyright (c) 2021, 2022 Systopia Lab, Computer Science, University of British Columbia
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

// used exernal dependencies
use nom::{
    bytes::complete::{tag, take_until, take_while},
    combinator::cut,
    error::Error,
    sequence::terminated,
    Err,
};

use crate::error::{IResult, VelosiLexerErrBuilder};
use crate::{SrcSpan, Token, VelosiToken, VelosiTokenKind};

/// parses and consumes an end of line comment `// foo`
pub fn linecomment(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
    // try to match the opening comment `//`, there is no match, return.
    let (input, _) = tag("//")(input)?;

    // match the rest of the line
    let (input, c) = take_while(|f: char| f != '\n')(input)?;

    // trim the whitespace around the comments.
    let comment = c.as_str().trim().to_string();

    Ok((input, Token::new(VelosiTokenKind::Comment(comment), c)))
}

/// parses and consumes a block comment `/* bar */`
///
/// The parser here currently does not support nested block comments.
/// the block comment must be closed again
pub fn blockcomment(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
    // try to match the opening comment keyword, there is no match, return.
    let (i1, c) = tag("/*")(input)?;

    // now match the block comment and discard following whitespace characters
    match cut(terminated(take_until("*/"), tag("*/")))(i1) {
        Ok((input, c)) => {
            // trim the whitespace around the comment
            let comment = c.as_str().trim().to_string();
            Ok((input, Token::new(VelosiTokenKind::BlockComment(comment), c)))
        }
        Err(e) => {
            let _e: Err<Error<SrcSpan>> = e;
            let errmsg = "unclosed block comment.";
            let err = VelosiLexerErrBuilder::new(errmsg.to_string())
                .add_hint("insert `*/` here to close the block comment.".to_string())
                .add_location(c)
                .build();
            Err(Err::Failure(err))
        }
    }
}

#[cfg(test)]
use crate::nom::Slice;

#[test]
fn parse_comment_tests_one_line() {
    let sp = SrcSpan::new("// foo bar".to_string());
    let rem = sp.slice(10..10);
    let c = sp.slice(2..);
    assert_eq!(
        linecomment(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::Comment("foo bar".to_string()), c)
        ))
    );
}

#[test]
fn parse_comment_tests_one_line_with_newline() {
    let sp = SrcSpan::new("// foo bar\n".to_string());
    let rem = sp.slice(10..11);
    let c = sp.slice(2..10);
    // the newline is part of the new string
    assert_eq!(rem.as_str(), "\n");
    assert_eq!(
        linecomment(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::Comment("foo bar".to_string()), c)
        ))
    );
}

#[test]
fn parse_comment_tests_twoline() {
    let sp = SrcSpan::new("// foo \nbar".to_string());
    let rem = sp.slice(7..11);
    let c = sp.slice(2..7);
    assert_eq!(rem.as_str(), "\nbar");
    assert_eq!(
        linecomment(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::Comment("foo".to_string()), c)
        ))
    );
}

#[test]
fn parse_blockcomment_test_one() {
    let sp = SrcSpan::new("/* foo bar */".to_string());
    let rem = sp.slice(13..13);
    let c = sp.slice(2..11);
    assert_eq!(rem.as_str(), "");
    assert_eq!(
        blockcomment(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::BlockComment("foo bar".to_string()), c)
        ))
    );
}
#[test]
fn parse_blockcomment_test_newline() {
    let sp = SrcSpan::new("/* foo \nbar */".to_string());
    let rem = sp.slice(14..14);
    let c = sp.slice(2..12);
    assert_eq!(rem.as_str(), "");
    assert_eq!(
        blockcomment(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::BlockComment("foo \nbar".to_string()), c)
        ))
    );
}

#[test]
fn parse_blockcomment_test_follow() {
    let sp = SrcSpan::new("/* foo */ bar".to_string());
    let rem = sp.slice(9..13);
    assert_eq!(rem.as_str(), " bar");
    let c = sp.slice(2..7);
    assert_eq!(
        blockcomment(sp),
        Ok((
            rem,
            Token::new(VelosiTokenKind::BlockComment("foo".to_string()), c)
        ))
    );
}

#[test]
fn parse_blockcomment_test_unclosed() {
    assert!(blockcomment(SrcSpan::new("/* foo \n bar\n".to_string())).is_err());
}
