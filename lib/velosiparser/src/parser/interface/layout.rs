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

//! # VelosiParser -- Interface Field Layout Parsing
//!
//! The field layout assings names to different bit slices.

// used external dependencies
use nom::{
    combinator::{cut, opt},
    multi::separated_list0,
    sequence::{delimited, preceded, terminated, tuple},
};

// used crate dependencies
use crate::error::IResult;
use crate::parser::terminals::*;
use crate::parsetree::{VelosiParseTreeFieldSlice, VelosiParseTreeInterfaceFieldNode};
use crate::VelosiTokenStream;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Field Layout Parsing
////////////////////////////////////////////////////////////////////////////////////////////////////

/// parses the layout of an interface filed
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized field layout as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `LAYOUT := KW_LAYOUT LBRACE LIST(SLICE, COMMA) COMMA? RBRACE;
///
///
/// # Examples
///
/// * `layout { 0..2 foo }`
///
pub fn layout(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceFieldNode> {
    let (i1, _) = kw_layout(input)?;

    let (i2, slices) = delimited(
        lbrace,
        terminated(separated_list0(comma, iface_field_slice), opt(comma)),
        cut(rbrace),
    )(i1)?;

    Ok((i2, VelosiParseTreeInterfaceFieldNode::Layout(slices)))
}

/// parses the bitfield slice of an interface field
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized bitslice as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `SLICE := NUM DOTDOT NUM IDENT`
///
///
/// # Examples
///
/// * `0 .. 2 foo`
///
pub fn iface_field_slice(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeFieldSlice> {
    let mut pos = input.clone();

    let (i1, (start, end, name)) = tuple((num, cut(preceded(dotdot, num)), cut(ident)))(input)?;

    pos.span_until_start(&i1);

    Ok((i1, VelosiParseTreeFieldSlice::new(start, end, name, pos)))
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
use std::fs;
#[cfg(test)]
use velosilexer::VelosiLexer;

#[cfg(test)]
use crate::{
    test_parse_and_check_fail, test_parse_and_compare_file_fail, test_parse_and_compare_ok,
};

#[test]
fn test_field_slice_ok() {
    test_parse_and_compare_ok!("0..1 foo", iface_field_slice);
    test_parse_and_compare_ok!("0..1 _", iface_field_slice);
    // doesn't make much sense, but should parse
    test_parse_and_compare_ok!("1..0 foo", iface_field_slice);
    test_parse_and_compare_ok!("100..0 foo", iface_field_slice);
}

#[test]
fn test_field_slice_fail() {
    // unsupported start
    test_parse_and_check_fail!("a .. 2 foo", iface_field_slice);
    // unsupported end
    test_parse_and_check_fail!("1 .. b foo", iface_field_slice);
    // wrong separator
    test_parse_and_check_fail!("1 - 1 foo", iface_field_slice);
    // incomplete
    test_parse_and_check_fail!("1  foo", iface_field_slice);
}

#[test]
fn test_field_slice_fail_error_msg() {
    test_parse_and_compare_file_fail!("interface/parts/layout_02_wrong_slice", iface_field_slice);
    test_parse_and_compare_file_fail!(
        "interface/parts/layout_03_invalid_slice_end",
        iface_field_slice
    );
}

#[test]
fn test_layout_ok() {
    // empty layout
    test_parse_and_compare_ok!("Layout { }", layout, "Layout {\n}");
    test_parse_and_compare_ok!("Layout { 0..1 foo }", layout, "Layout {\n  0..1 foo,\n}");
    test_parse_and_compare_ok!(
        "Layout { 0..1 foo, 1..2 bar }",
        layout,
        "Layout {\n  0..1 foo,\n  1..2 bar,\n}"
    );

    // trailing comma
    test_parse_and_compare_ok!("Layout { 0..1 foo, }", layout, "Layout {\n  0..1 foo,\n}");
    test_parse_and_compare_ok!(
        "Layout { 0..1 foo, 1..2 bar, }",
        layout,
        "Layout {\n  0..1 foo,\n  1..2 bar,\n}"
    );
}

#[test]
fn test_layout_fail() {
    // wrong separator
    test_parse_and_check_fail!("Layout { 0..1 foo; 1..2 bar }", layout);
    // no separator
    test_parse_and_check_fail!("Layout { 0..1 foo  1..2 bar }", layout);
}

#[test]
fn test_layout_fail_error_msg() {
    test_parse_and_compare_file_fail!("interface/parts/layout_00_missing_separator", layout);
    test_parse_and_compare_file_fail!("interface/parts/layout_01_wrong_separator", layout);
}
