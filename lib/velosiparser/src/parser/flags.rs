// VelosiParser -- Parser for the VelosiRaptor specification language
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

//! Flags Parser
//!
//! Parses a Flag definition

// the used nom functionality
use nom::{
    combinator::{cut, opt},
    multi::separated_list0,
    sequence::{delimited, tuple},
};

// the used library-internal functionaltity
use crate::error::IResult;
use crate::parser::terminals::{assign, comma, ident, kw_flags, lbrace, rbrace, semicolon};
use crate::parsetree::VelosiParseTreeFlags;
use crate::VelosiTokenStream;

/// parses flags
///
/// # Arguments
///
/// # Return Value
///
/// # Grammar
///
/// `FLAGS := KW_FLAGS LBRACE LIST(COMMA, IDENT) RBRACE`
pub fn flags(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeFlags> {
    let mut pos = input.clone();
    // parse the `flags` keyword, return otherwise
    let (i1, _) = kw_flags(input)?;

    let flagsblock = delimited(
        lbrace,
        separated_list0(comma, ident),
        tuple((opt(comma), rbrace)),
    );

    let (i2, flags) = cut(flagsblock)(i1)?;
    pos.span_until_start(&i2);

    Ok((i2, VelosiParseTreeFlags::new(flags, pos)))
}

/// parses flags in the unit context
///
/// # Arguments
///
/// # Return Value
///
/// # Grammar
///
/// `FLAGS := KW_FLAGS LBRACE LIST(COMMA, IDENT) RBRACE`
pub fn flags_unit(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeFlags> {
    let mut pos = input.clone();
    // parse the `flags` keyword, return otherwise
    let (i1, _) = kw_flags(input)?;

    let flagsblock = delimited(
        lbrace,
        separated_list0(comma, ident),
        tuple((opt(comma), rbrace)),
    );

    let (i2, flags) = cut(delimited(assign, flagsblock, semicolon))(i1)?;
    pos.span_until_start(&i2);

    Ok((i2, VelosiParseTreeFlags::new(flags, pos)))
}

#[cfg(test)]
use crate::VelosiLexer;

#[test]
fn test_ok() {
    let content = "flags = { FOO, BAR }; ";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(flags_unit(ts).is_ok());

    let content = "flags = { FOO, BAR, }; ";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(flags_unit(ts).is_ok());

    let content = "flags { FOO, BAR }";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(flags(ts).is_ok());

    let content = "flags { FOO, BAR, }";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(flags(ts).is_ok());
}
