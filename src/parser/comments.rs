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
pub fn comment(input: SourcePos) -> IResult<SourcePos, SourcePos> {
    // Matches a inline comment `//`, does not consume the `\n` character
    let (input, (_, c)) = pair(tag(tokens::COMMENT), is_not(tokens::EOL))(input)?;
    println!("{}", input);
    println!("{}", c);
    // return the remainder of the input, and the parsed comment value
    Ok((input, c))
}

/// parses and consumes a block comment `/* bar */`
/// TODO: this doesn't work with nested comments!
pub fn blockcomment(input: SourcePos) -> IResult<SourcePos, SourcePos> {
    let (input, (_, c, _)) = tuple((
        // start with the block comment start token
        tag(tokens::COMMENT_BLOCK_START),
        // consume everything until we reach the end of token
        take_until(tokens::COMMENT_BLOCK_END),
        // consume the end token
        tag(tokens::COMMENT_BLOCK_END),
    ))(input)?;
    Ok((input, c))
}

#[test]
fn parse_comment_tests() {
    assert_eq!(
        comment(SourcePos::new("stdin", b"// foo bar")),
        Ok((
            SourcePos::new_at("stdin", b"", 10, 1, 11),
            SourcePos::new_at("stdin", b" foo bar", 2, 1, 3),
        ))
    );

    assert_eq!(
        comment(SourcePos::new("stdin", b"// foo \nbar")),
        Ok((
            SourcePos::new_at("stdin", b"\nbar", 8, 1, 9),
            SourcePos::new_at("stdin", b" foo", 2, 1, 1),
        ))
    );
    assert_eq!(
        comment(SourcePos::new("stdin", b"// foo bar\n\n")),
        Ok((
            SourcePos::new_at("stdin", b"bar", 11, 2, 4),
            SourcePos::new_at("stdin", b" foo\n", 1, 1, 1),
        ))
    );
}

#[test]
fn parse_blockcomment_tests() {
    assert_eq!(
        blockcomment(SourcePos::new("stdin", b"/* foo bar */")),
        Ok((
            SourcePos::new_at("stdin", b"bar", 11, 2, 4),
            SourcePos::new_at("stdin", b" foo\n", 1, 1, 1),
        ))
    );
    assert_eq!(
        blockcomment(SourcePos::new("stdin", b"/* foo \nbar */")),
        Ok((
            SourcePos::new_at("stdin", b"", 11, 2, 1),
            SourcePos::new_at("stdin", b" foo\nbar ", 1, 1, 1),
        ))
    );
    assert_eq!(
        blockcomment(SourcePos::new("stdin", b"/* foo  */bar")),
        Ok((
            SourcePos::new_at("stdin", b"bar", 11, 2, 4),
            SourcePos::new_at("stdin", b" foo\n", 1, 1, 1),
        ))
    );
    assert_eq!(
        blockcomment(SourcePos::new("stdin", b"/* foo  */\nbar")),
        Ok((
            SourcePos::new_at("stdin", b"bar", 11, 2, 4),
            SourcePos::new_at("stdin", b" foo\n", 1, 1, 1),
        ))
    );
}
