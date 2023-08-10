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

//! # VelosiParser: Flags
//!
//! Parses permission and access mode flags in the global and unit context

// external dependencies
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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Flags Parsers
////////////////////////////////////////////////////////////////////////////////////////////////////

/// parses flags in the global context
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `FLAGS := KW_FLAGS LBRACE LIST(COMMA, IDENT) RBRACE`
///
/// # Examples
///
/// `flags { read, write }`
///
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
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `FLAGS := KW_FLAGS ASSIGN LBRACE LIST(COMMA, IDENT) RBRACE SEMICOLON`
///
/// # Examples
///
/// `flags = { read, write };`
///
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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
use velosilexer::VelosiLexer;

#[cfg(test)]
use crate::{test_parse_and_check_fail, test_parse_and_compare_ok};

#[test]
fn test_flags_global_ok() {
    test_parse_and_compare_ok!("flags { foo, bar }", flags, "flags = { foo, bar };");
    test_parse_and_compare_ok!("flags { FOO, BAR }", flags, "flags = { FOO, BAR };");

    // with trailing comma
    test_parse_and_compare_ok!("flags { foo, bar, }", flags, "flags = { foo, bar };");
    test_parse_and_compare_ok!("flags { FOO, BAR, }", flags, "flags = { FOO, BAR };");

    // empty flags
    test_parse_and_compare_ok!("flags { }", flags, "flags = {  };");

    // repetition
    test_parse_and_compare_ok!("flags { FOO, FOO, }", flags, "flags = { FOO, FOO };");
}

#[test]
fn test_flags_global_fail() {
    test_parse_and_check_fail!("flags { FOO FOO }", flags);
    test_parse_and_check_fail!("flags { FOO FOO, }", flags);
    test_parse_and_check_fail!("flags { 1, foo(), }", flags);
    test_parse_and_check_fail!("flags = { FOO FOO, };", flags);
}

#[test]
fn test_flags_unit_ok() {
    test_parse_and_compare_ok!("flags = { foo, bar };", flags_unit, "flags = { foo, bar };");
    test_parse_and_compare_ok!("flags = { FOO, BAR };", flags_unit, "flags = { FOO, BAR };");

    // with trailing comma
    test_parse_and_compare_ok!(
        "flags = { foo, bar, };",
        flags_unit,
        "flags = { foo, bar };"
    );
    test_parse_and_compare_ok!(
        "flags = { FOO, BAR, };",
        flags_unit,
        "flags = { FOO, BAR };"
    );

    // empty flags
    test_parse_and_compare_ok!("flags = { };", flags_unit, "flags = {  };");

    // repetition
    test_parse_and_compare_ok!(
        "flags = { FOO, FOO, };",
        flags_unit,
        "flags = { FOO, FOO };"
    );
}

#[test]
fn test_flags_unit_fail() {
    test_parse_and_check_fail!("flags = { FOO FOO };", flags_unit);
    test_parse_and_check_fail!("flags = { FOO FOO, };", flags_unit);
    test_parse_and_check_fail!("flags = { 1, foo(), };", flags_unit);
    test_parse_and_check_fail!("flags { FOO, BAR }", flags_unit);
}
