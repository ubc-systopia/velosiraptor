// VelosiParser -- Parser for the VelosiRaptor specification language
//
//
// MIT License
//
// Copyright (c) 2021-2023 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiParser: Parameters
//!
//! This module contains the parser for parameters of methods and other variable declarations

// external dependencies
use nom::{
    combinator::{cut, opt},
    multi::separated_list0,
    sequence::{delimited, preceded},
};

// used carate functinality
use crate::error::IResult;
use crate::parser::terminals::{colon, comma, ident, lparen, rparen, typeinfo};
use crate::parsetree::VelosiParseTreeParam;
use crate::VelosiTokenStream;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Parameter Parsing
////////////////////////////////////////////////////////////////////////////////////////////////////

/// parses a single parameter
///
/// This function parses a single, typed parameter
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized method definition as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `ARG     := IDENT COLON TYPE`
///
/// # Examples
///
/// * `a : bool`
///
pub fn param(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeParam> {
    let mut pos = input.clone();

    // parse the identifier of the parameter
    let (i1, name) = ident(input)?;

    // next, parse the type info
    let (i2, ptype) = cut(preceded(colon, typeinfo))(i1)?;

    // create the token stream covering the entire method def
    pos.span_until_start(&i2);

    // return the result
    Ok((i2, VelosiParseTreeParam::new(name, ptype, pos)))
}

/// Parses and consumes a comma separated list of parameters
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized parameter list definition as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # GRAMMAR
///
/// `PARAM_LIST := LPAREN SEPLIST(COMMA, PARAMETER) RPAREN
///
pub fn param_list(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, Vec<VelosiParseTreeParam>> {
    let (i, p) = opt(delimited(
        lparen,
        cut(separated_list0(comma, param)),
        cut(rparen),
    ))(input)?;
    Ok((i, p.unwrap_or_default()))
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
    test_parse_and_check_fail, test_parse_and_check_ok, test_parse_and_compare_file_fail,
    test_parse_and_compare_ok,
};

#[test]
fn test_parameter_ok() {
    test_parse_and_compare_ok!("foo: bool", param);
    test_parse_and_compare_ok!("foo: int", param);
    test_parse_and_compare_ok!("foo: MyUnit", param);
}

#[test]
fn test_parameter_fail() {
    test_parse_and_check_fail!("foo : 1", param);
    test_parse_and_check_fail!("foo 1", param);
    test_parse_and_check_fail!("bool foo", param);
    test_parse_and_check_fail!("bool : foo", param);
}

#[test]
fn test_parameter_list_ok() {
    // empty
    test_parse_and_check_ok!("()", param_list);
    // one param
    test_parse_and_check_ok!("(base: addr)", param_list);
    // two params
    test_parse_and_check_ok!("(base: addr, base2: addr)", param_list);
}

#[test]
fn test_paramter_list_fail() {
    // no type
    test_parse_and_check_fail!("(base)", param_list);
    // no separator
    test_parse_and_check_fail!("(base: addr base2: addr)", param_list);
    // wrong separator
    test_parse_and_check_fail!("(base: addr; base2: addr)", param_list);
}

#[test]
fn test_paramter_list_fail_error_msg() {
    test_parse_and_compare_file_fail!("params/param_list_00_wrong_separator", param_list);
    test_parse_and_compare_file_fail!("params/param_list_01_no_separator", param_list);
}
