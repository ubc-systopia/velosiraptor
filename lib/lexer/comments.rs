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

// the used nom componets
use nom::{
    bytes::complete::{is_not, tag, take_until},
    sequence::terminated,
    IResult,
};

use super::sourcepos::SourcePos;
use super::token::{Token, TokenContent};

/// parses and consumes an end of line comment '// foo
pub fn linecomment(input: SourcePos) -> IResult<SourcePos, Token> {
    // try to match the opening comment `//`, there is no match, return.
    let input = match tag("//")(input) {
        Ok((input, _)) => input,
        Err(x) => return Err(x),
    };

    // Matches a inline comment `// foobar`
    match is_not("\n")(input) {
        Ok((input, c)) => Ok((
            input,
            Token::new(TokenContent::Comment(c.as_str().trim().to_string()), c),
        )),
        Err(x) => Err(x),
    }
}

/// parses and consumes a block comment `/* bar */`
/// TODO: this doesn't work with nested comments!
pub fn blockcomment(input: SourcePos) -> IResult<SourcePos, Token> {
    // try to match the opening comment keyword, there is no match, return.
    let input = match tag("/*")(input) {
        Ok((input, _)) => input,
        Err(x) => return Err(x),
    };

    // now match the block comment and discard following whitespace characters
    match terminated(take_until("*/"), tag("*/"))(input) {
        Ok((input, c)) => Ok((
            input,
            Token::new(TokenContent::Comment(c.as_str().trim().to_string()), c),
        )),
        Err(e) => Err(e),
    }
}

#[cfg(test)]
use crate::nom::Slice;

#[test]
fn parse_comment_tests_one_line() {
    let sp = SourcePos::new("stdin", "// foo bar");
    let rem = sp.slice(10..10);
    let c = sp.slice(2..);
    assert_eq!(
        linecomment(sp),
        Ok((
            rem,
            Token::new(TokenContent::Comment("foo bar".to_string()), c)
        ))
    );
}

#[test]
fn parse_comment_tests_one_line_with_newline() {
    let sp = SourcePos::new("stdin", "// foo bar\n");
    let rem = sp.slice(10..11);
    let c = sp.slice(2..10);
    // the newline is part of the new string
    assert_eq!(rem.as_str(), "\n");
    assert_eq!(
        linecomment(sp),
        Ok((
            rem,
            Token::new(TokenContent::Comment("foo bar".to_string()), c)
        ))
    );
}

#[test]
fn parse_comment_tests_twoline() {
    let sp = SourcePos::new("stdin", "// foo \nbar");
    let rem = sp.slice(7..11);
    let c = sp.slice(2..7);
    assert_eq!(rem.as_str(), "\nbar");
    assert_eq!(
        linecomment(sp),
        Ok((rem, Token::new(TokenContent::Comment("foo".to_string()), c)))
    );
}

#[test]
fn parse_blockcomment_test_one() {
    let sp = SourcePos::new("stdin", "/* foo bar */");
    let rem = sp.slice(13..13);
    let c = sp.slice(2..11);
    assert_eq!(rem.as_str(), "");
    assert_eq!(
        blockcomment(sp),
        Ok((
            rem,
            Token::new(TokenContent::Comment("foo bar".to_string()), c)
        ))
    );
}
#[test]
fn parse_blockcomment_test_newline() {
    let sp = SourcePos::new("stdin", "/* foo \nbar */");
    let rem = sp.slice(14..14);
    let c = sp.slice(2..12);
    assert_eq!(rem.as_str(), "");
    assert_eq!(
        blockcomment(sp),
        Ok((
            rem,
            Token::new(TokenContent::Comment("foo \nbar".to_string()), c)
        ))
    );
}

#[test]
fn parse_blockcomment_test_follow() {
    let sp = SourcePos::new("stdin", "/* foo */ bar");
    let rem = sp.slice(9..13);
    assert_eq!(rem.as_str(), " bar");
    let c = sp.slice(2..7);
    assert_eq!(
        blockcomment(sp),
        Ok((rem, Token::new(TokenContent::Comment("foo".to_string()), c)))
    );
}

#[test]
fn parse_blockcomment_test_unclosed() {
    assert!(blockcomment(SourcePos::new("stdin", "/* foo \n bar\n")).is_err());
}
