// VelosiParser -- Parser for the VelosiRaptor specification language
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiParser: State Fields

// external dependencies
use nom::{
    branch::alt,
    combinator::{cut, opt},
    multi::separated_list0,
    sequence::{delimited, preceded, terminated, tuple},
    Err,
};

// used crate functinality
use crate::error::{IResult, VelosiParserErrBuilder};
use crate::parser::terminals::{
    comma, dotdot, ident, kw_mem, kw_reg, lbrace, lbrack, num, rbrace, rbrack,
};
use crate::parsetree::{
    VelosiParseTreeFieldSlice, VelosiParseTreeIdentifier, VelosiParseTreeStateField,
    VelosiParseTreeStateFieldMemory, VelosiParseTreeStateFieldRegister,
};
use crate::{VelosiParserErr, VelosiTokenStream};

////////////////////////////////////////////////////////////////////////////////////////////////////
// State Field Parsing
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Parses a State Field Definition
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized state field definition as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `STATEFIELD := MEMORYFIELD | REGISTERFIELD`
///
/// # Example
///
/// * `mem foo [ base, 0, 8 ]`
/// * `reg bar [ 8 ]`
///
pub fn statefield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeStateField> {
    alt((memoryfield, registerfield))(input)
}

/// Parses the memory field definition of the state
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized memory field definition as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `MEMORYFIELD := KW_MEM IDENT STATEFIELDINFO (LBRACE SEPLIST(COMMA, STATEFIELDSLICE) RBRACE)?`
///
/// # Example
///
/// * `mem foo [ base, 0, 8 ]`
/// * `mem foo [ base, 0, 8 ] { 0 .. 64 foo }`
///
fn memoryfield(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeStateField> {
    let mut pos = input.clone();

    // if we have the memory keyword
    let (i1, _) = kw_mem(input)?;

    let (i2, (name, fieldinfo)) = cut(tuple((ident, delimited(lbrack, memfieldinfo, rbrack))))(i1)?;

    let (i3, slices) = opt(delimited(
        lbrace,
        terminated(separated_list0(comma, statefieldslice), opt(comma)),
        cut(rbrace),
    ))(i2)?;

    pos.span_until_start(&i3);

    let slices = if let Some(slices) = slices {
        if slices.is_empty() {
            return Err(empty_field_err(i3));
        }
        slices
    } else {
        Vec::new()
    };

    let (base, offset, size) = fieldinfo;

    let res = VelosiParseTreeStateFieldMemory::new(name, base, offset, size, slices, pos);
    Ok((i3, VelosiParseTreeStateField::Memory(res)))
}

type MemFiledInfo = (VelosiParseTreeIdentifier, u64, u64);

/// Parses the memory field information block
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized memfield info as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `STATEFIELDINFO := LBRACK IDENT NUM NUM RBRACK`
///
fn memfieldinfo(input: VelosiTokenStream) -> IResult<VelosiTokenStream, MemFiledInfo> {
    tuple((terminated(ident, comma), terminated(num, comma), num))(input)
}

/// Parses a register field definitin of the state
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized register field description as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `STATEFIELD := IDENT STATEFIELDINFO (LBRACE SEPLIST(COMMA, STATEFIELDSLICE) RBRACE)?`
///
/// # Examples
///
/// * `reg foo [ 8 ]`
/// * `reg foo [ 8 ] { 0 .. 64 foo }`
///
fn registerfield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeStateField> {
    let mut pos = input.clone();

    // if we have the memory keyword
    let (i1, _) = kw_reg(input)?;

    let (i2, (name, size)) = cut(tuple((ident, delimited(lbrack, num, rbrack))))(i1)?;

    let (i3, slices) = opt(delimited(
        lbrace,
        terminated(separated_list0(comma, statefieldslice), opt(comma)),
        cut(rbrace),
    ))(i2)?;

    pos.span_until_start(&i3);

    let slices = if let Some(slices) = slices {
        if slices.is_empty() {
            return Err(empty_field_err(i3));
        }
        slices
    } else {
        Vec::new()
    };

    let res = VelosiParseTreeStateFieldRegister::new(name, size, slices, pos);
    Ok((i3, VelosiParseTreeStateField::Register(res)))
}

/// Helper function to display an error message for an empty state field block
fn empty_field_err(loc: VelosiTokenStream) -> Err<VelosiParserErr> {
    let errmsg = "empty state field block";
    let hint = "remove the block or fill it in explicitly";
    let err = VelosiParserErrBuilder::new(errmsg.to_string())
        .add_tokstream(loc)
        .add_hint(hint.to_string())
        .build();
    Err::Failure(err)
}

/// Parses the state field slice definition
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized state field slice definitions as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `STATEFIELDSLICE := NUM DOTDOT NUM IDENT`
///
/// # Examples
///
///  * `0 .. 1 foo`
///
fn statefieldslice(
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
fn test_slice_ok() {
    test_parse_and_compare_ok!("0..1 foo", statefieldslice);
    // the parser doesn't care about the ordering of the start and end
    test_parse_and_compare_ok!("1..0 foo", statefieldslice);
    test_parse_and_compare_ok!("1000..2000 foo", statefieldslice);
}

#[test]
fn test_slice_fail() {
    // wrong separator
    test_parse_and_check_fail!("a..1 foo", statefieldslice);
    test_parse_and_check_fail!("1..a foo", statefieldslice);
}

#[test]
fn test_stateregister_field_ok() {
    test_parse_and_compare_ok!("reg foo [ 8 ]", registerfield, "reg foo [ 8 ]");

    test_parse_and_compare_ok!(
        "reg foo [ 8 ] { 0 .. 1 foo }",
        registerfield,
        "reg foo [ 8 ] {\n  0..1 foo,\n}"
    );

    test_parse_and_compare_ok!(
        "reg foo [ 8 ] { 0 .. 1 foo, 0 ..1 bar }",
        registerfield,
        "reg foo [ 8 ] {\n  0..1 foo,\n  0..1 bar,\n}"
    );
}

#[test]
fn test_stateregister_field_fail() {
    // empty body
    test_parse_and_check_fail!("reg foo [ 8 ] { }", registerfield);
    // wrong information on the register field
    test_parse_and_check_fail!("reg foo [ base, 8, 8 ]", registerfield);
    // wrong information on the register field
    test_parse_and_check_fail!("reg foo [ 8, 8, base ] { }", registerfield);
    test_parse_and_check_fail!("reg foo [ 8 ] { 0 .. 1 foo 0 ..1 bar }", registerfield);
}

#[test]
fn test_staterregister_field_fail_error_msg() {
    // empty field definition
    test_parse_and_compare_file_fail!("state/parts/registerfield_00_empty_body", registerfield);

    // memory field information instead of register field information
    test_parse_and_compare_file_fail!(
        "state/parts/registerfield_01_field_info_wrong",
        registerfield
    );
    test_parse_and_compare_file_fail!(
        "state/parts/registerfield_02_field_info_wrong_2",
        registerfield
    );
}

#[test]
fn test_statememory_field_ok() {
    test_parse_and_compare_ok!(
        "mem foo [ base, 8, 8 ]",
        memoryfield,
        "mem foo [ base, 8, 8 ]"
    );

    test_parse_and_compare_ok!(
        "mem foo [ base, 8, 8 ] { 0 .. 1 foo }",
        memoryfield,
        "mem foo [ base, 8, 8 ] {\n  0..1 foo,\n}"
    );

    test_parse_and_compare_ok!(
        "mem foo [ base, 8, 8 ] { 0 .. 1 foo, 0 ..1 bar }",
        memoryfield,
        "mem foo [ base, 8, 8 ] {\n  0..1 foo,\n  0..1 bar,\n}"
    );
}

#[test]
fn test_statermemory_field_fail() {
    // empty body
    test_parse_and_check_fail!("mem foo [  base, 8, 8  ] { }", memoryfield);
    // wrong information on the memory field
    test_parse_and_check_fail!("mem foo [ 8 ]", memoryfield);
    // wrong information on the memory field
    test_parse_and_check_fail!("mem foo [ 8, 8, base ]", memoryfield);
    test_parse_and_check_fail!(
        "mem foo [ base, 8, 8 ] { 0 .. 1 foo 0 ..1 bar }",
        memoryfield
    );
}

#[test]
fn test_statememory_field_fail_error_messages() {
    // empty field definition
    test_parse_and_compare_file_fail!("state/parts/memoryfield_00_empty_body", memoryfield);

    // memory field information instead of register field information
    test_parse_and_compare_file_fail!("state/parts/memoryfield_01_field_info_wrong", memoryfield);
    test_parse_and_compare_file_fail!("state/parts/memoryfield_02_field_info_wrong_2", memoryfield);
}
