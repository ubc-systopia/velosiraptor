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

//! specifies special parsing tokens for velosiraptor.

/// represents the end of line string.
pub const EOL: &str = "\n";

/// represents the start of a end of line comment
pub const COMMENT: &str = "//";

/// represents the start of a block comment
pub const COMMENT_BLOCK_START: &str = "/*";

/// represents the end of a block comment
pub const COMMENT_BLOCK_END: &str = "*/";

/// represents the import keyword
pub const IMPORT: &str = "import";

/// represents the import keyword
pub const UNIT: &str = "unit";

/// represents the end-of-statement token
pub const EOS: &str = ";";

/// start of block token
pub const BLOCK_START: &str = "{";

/// end of block token
pub const BLOCK_END: &str = "}";

use super::SourcePos;
use nom::bytes::complete::tag;
use nom::character::complete::multispace0;
use nom::sequence::tuple;
use nom::IResult;

/// parse an opening bracket `[` surrounded by whitespace
pub fn lbrack(input: SourcePos) -> IResult<SourcePos, SourcePos> {
    // match any of the comments above
    match tuple((multispace0, tag("["), multispace0))(input) {
        Ok((input, _)) => Ok((input, SourcePos::empty())),
        Err(x) => Err(x),
    }
}

/// parse a closing bracket `]` surrounded by whitespace
pub fn rbrack(input: SourcePos) -> IResult<SourcePos, SourcePos> {
    // match any of the comments above
    match tuple((multispace0, tag("]"), multispace0))(input) {
        Ok((input, _)) => Ok((input, SourcePos::empty())),
        Err(x) => Err(x),
    }
}

/// parse an opening brace `{` surrounded by whitespace
pub fn lbrace(input: SourcePos) -> IResult<SourcePos, SourcePos> {
    // match any of the comments above
    match tuple((multispace0, tag("{"), multispace0))(input) {
        Ok((input, _)) => Ok((input, SourcePos::empty())),
        Err(x) => Err(x),
    }
}

/// parse a closing brace `}` surrounded by whitespace
pub fn rbrace(input: SourcePos) -> IResult<SourcePos, SourcePos> {
    // match any of the comments above
    match tuple((multispace0, tag("}"), multispace0))(input) {
        Ok((input, _)) => Ok((input, SourcePos::empty())),
        Err(x) => Err(x),
    }
}

/// parse a comma `,` surrounded by whitespace
pub fn comma(input: SourcePos) -> IResult<SourcePos, SourcePos> {
    // match any of the comments above
    match tuple((multispace0, tag(","), multispace0))(input) {
        Ok((input, _)) => Ok((input, SourcePos::empty())),
        Err(x) => Err(x),
    }
}

/// parse a comma `,` surrounded by whitespace, discards parsing output
pub fn semicolon(input: SourcePos) -> IResult<SourcePos, SourcePos> {
    // match any of the comments above
    match tuple((multispace0, tag(";"), multispace0))(input) {
        Ok((input, _)) => Ok((input, SourcePos::empty())),
        Err(x) => Err(x),
    }
}
