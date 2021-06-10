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
    sequence::{pair, tuple},
    IResult,
};

// get the tokens
use super::tokens;
use super::SourcePos;

/// parses and consumes an end of line comment '// foo
pub fn comment(input: SourcePos) -> IResult<SourcePos, ()> {
    // Matches a inline comment `//`, does not consume the `\n` character
    let (input, _) = pair(tag(tokens::COMMENT), is_not(tokens::EOL))(input)?;
    // return the remainder of the input, and the parsed comment value
    Ok((input, ()))
}

/// parses and consumes a block comment `/* bar */`
/// TODO: this doesn't work with nested comments!
pub fn blockcomment(input: SourcePos) -> IResult<SourcePos, ()> {
    let (input, (_, c, _)) = tuple((
        // start with the block comment start token
        tag(tokens::COMMENT_BLOCK_START),
        // consume everything until we reach the end of token
        take_until(tokens::COMMENT_BLOCK_END),
        // consume the end token
        tag(tokens::COMMENT_BLOCK_END),
    ))(input)?;
    Ok((input, ()))
}

#[test]
fn parse_comment_tests_one_line() {
    assert_eq!(
        comment(SourcePos::new("stdin", "// foo bar")),
        Ok((SourcePos::new_at("stdin", "", 10, 1, 11), (),))
    );
}

#[test]
fn parse_comment_tests_one_line_with_newline() {
    assert_eq!(
        comment(SourcePos::new("stdin", "// foo bar\n")),
        Ok((SourcePos::new_at("stdin", "\n", 10, 1, 11), (),))
    );
}

#[test]
fn parse_comment_tests_twoline() {
    assert_eq!(
        comment(SourcePos::new("stdin", "// foo \nbar")),
        Ok((SourcePos::new_at("stdin", "\nbar", 7, 1, 8), (),))
    );
}

#[test]
fn parse_blockcomment_test_one() {
    assert_eq!(
        blockcomment(SourcePos::new("stdin", "/* foo bar */")),
        Ok((SourcePos::new_at("stdin", "", 13, 1, 14), (),))
    );
}
#[test]
fn parse_blockcomment_test_newline() {
    assert_eq!(
        blockcomment(SourcePos::new("stdin", "/* foo \nbar */")),
        Ok((SourcePos::new_at("stdin", "", 14, 2, 7), ()))
    );
}

#[test]
fn parse_blockcomment_test_follow() {
    assert_eq!(
        blockcomment(SourcePos::new("stdin", "/* foo */ bar")),
        Ok((SourcePos::new_at("stdin", " bar", 9, 1, 10), ()))
    );
}
