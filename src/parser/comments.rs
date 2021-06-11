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
    branch::alt,
    bytes::complete::{is_not, tag, take_until},
    character::complete::multispace0,
    multi::many0,
    sequence::{terminated, tuple},
    IResult,
};

// get the tokens
use super::tokens;
use super::SourcePos;

/// parses and consumes an end of line comment '// foo
pub fn parse_comment(input: SourcePos) -> IResult<SourcePos, SourcePos> {
    // Matches a inline comment `//`, does not consume whitespace after
    let comment = tuple((
        // start with the comment
        tag(tokens::COMMENT),
        // until we hit end of line
        is_not(tokens::EOL),
    ));

    // now match the end of line comment with possible multispace following
    match terminated(comment, multispace0)(input) {
        Ok((input, _)) => Ok((input, SourcePos::empty())),
        Err(x) => Err(x),
    }
}

/// parses and consumes a block comment `/* bar */`
/// TODO: this doesn't work with nested comments!
pub fn parse_blockcomment(input: SourcePos) -> IResult<SourcePos, SourcePos> {
    // build the blockcomment parser, does not consume whitespace after
    let blockcomment = tuple((
        // start with the block comment start token
        tag(tokens::COMMENT_BLOCK_START),
        // consume everything until we reach the end of token
        take_until(tokens::COMMENT_BLOCK_END),
        // consume the end token
        tag(tokens::COMMENT_BLOCK_END),
    ));

    // now match the block comment and discard following whitespace characters
    match terminated(blockcomment, multispace0)(input) {
        Ok((input, _)) => Ok((input, SourcePos::empty())),
        Err(x) => Err(x),
    }
}

/// parse zero or more of the possible comment types
pub fn parse_comments(input: SourcePos) -> IResult<SourcePos, SourcePos> {
    // match any of the comments above
    match many0(alt((parse_blockcomment, parse_comment)))(input) {
        Ok((input, _)) => Ok((input, SourcePos::empty())),
        Err(x) => Err(x),
    }
}

#[test]
fn parse_comment_tests_one_line() {
    assert_eq!(
        parse_comment(SourcePos::new("stdin", "// foo bar")),
        Ok((
            SourcePos::new_at("stdin", "", 10, 1, 11),
            SourcePos::empty()
        ))
    );
}

#[test]
fn parse_comment_tests_one_line_with_newline() {
    assert_eq!(
        parse_comment(SourcePos::new("stdin", "// foo bar\n")),
        Ok((SourcePos::new_at("stdin", "", 11, 2, 1), SourcePos::empty()))
    );
}

#[test]
fn parse_comment_tests_twoline() {
    assert_eq!(
        parse_comment(SourcePos::new("stdin", "// foo \nbar")),
        Ok((
            SourcePos::new_at("stdin", "bar", 8, 2, 1),
            SourcePos::empty()
        ))
    );
}

#[test]
fn parse_blockcomment_test_one() {
    assert_eq!(
        parse_blockcomment(SourcePos::new("stdin", "/* foo bar */")),
        Ok((
            SourcePos::new_at("stdin", "", 13, 1, 14),
            SourcePos::empty()
        ))
    );
}
#[test]
fn parse_blockcomment_test_newline() {
    assert_eq!(
        parse_blockcomment(SourcePos::new("stdin", "/* foo \nbar */")),
        Ok((SourcePos::new_at("stdin", "", 14, 2, 7), SourcePos::empty()))
    );
}

#[test]
fn parse_blockcomment_test_follow() {
    assert_eq!(
        parse_blockcomment(SourcePos::new("stdin", "/* foo */ bar")),
        Ok((
            SourcePos::new_at("stdin", "bar", 10, 1, 11),
            SourcePos::empty()
        ))
    );
}

#[test]
fn parse_any_comments_test() {
    assert_eq!(
        parse_comments(SourcePos::new("stdin", "// abc\n /* foo */ // more \n bar")),
        Ok((
            SourcePos::new_at("stdin", "bar", 28, 3, 2),
            SourcePos::empty()
        ))
    );
}
