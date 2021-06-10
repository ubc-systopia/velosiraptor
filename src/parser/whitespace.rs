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
    bytes::complete::is_a, character::complete::multispace0, error::ParseError,
    sequence::delimited, IResult,
};

// get the tokens
use super::tokens;
use super::SourcePos;

/// parses whitespace characters
pub fn whitespace(input: SourcePos) -> IResult<SourcePos, ()> {
    let (input, _) = is_a(tokens::WHITESPACE)(input)?;
    Ok((input, ()))
}

fn ws<'a, F: 'a, O, E: ParseError<SourcePos<'a>>>(
    inner: F,
) -> impl FnMut(SourcePos<'a>) -> IResult<SourcePos<'a>, SourcePos<'a>, E>
where
    F: Fn(SourcePos<'a>) -> IResult<SourcePos, SourcePos, E>,
{
    delimited(multispace0, inner, multispace0)
}

#[test]
fn parse_white_tests_prefix() {
    assert_eq!(
        whitespace(SourcePos::new("stdin", "     foo bar")),
        Ok((SourcePos::new_at("stdin", "foo bar", 5, 1, 6), (),))
    );
}

#[test]
fn parse_white_tests_prefix_newlines() {
    assert_eq!(
        whitespace(SourcePos::new("stdin", " \n \n foo bar")),
        Ok((SourcePos::new_at("stdin", "foo bar", 5, 3, 2), (),))
    );
}
