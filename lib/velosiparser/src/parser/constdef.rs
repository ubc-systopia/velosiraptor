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

//! # VelosiParser: Constant Definitions
//!
//! This module contains the parser for constant definitions either globally or within the
//! unit contexts.

// external dependencies
use nom::{
    combinator::cut,
    sequence::{delimited, pair, terminated},
};

// used crate functionality
use crate::error::IResult;
use crate::parser::expr::expr;
use crate::parser::terminals::{assign, colon, ident, kw_const, semicolon, typeinfo};
use crate::parsetree::VelosiParseTreeConstDef;
use crate::VelosiTokenStream;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Constant Parsing
////////////////////////////////////////////////////////////////////////////////////////////////////

/// parses and consumes an constant definition
///
/// The constant definition assigns a name to a constant value.
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized constant definition as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `CONSTDEF := KW_CONST IDENT COLON TYPE ASSIGN EXPR SEMICOLON;`
///
/// # Examples
///
///  * `const FOO : int = 1234;`
///  * `const BAR : int = 1234 + FOO;`
///
pub fn constdef(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeConstDef> {
    let mut pos = input.clone();

    // parse the `const` keyword, return otherwise
    let (i1, _) = kw_const(input)?;

    // parse the type information `IDENT : TYPE =`
    let (i2, (ident, ti)) = cut(pair(ident, delimited(colon, typeinfo, assign)))(i1)?;

    // parse the expression `EXPR SEMICOLON`
    let (i3, valexpr) = cut(terminated(expr, semicolon))(i2)?;

    // create the token stream covering the entire const def
    pos.span_until_start(&i3);
    Ok((i3, VelosiParseTreeConstDef::new(ident, ti, valexpr, pos)))
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
use velosilexer::VelosiLexer;

#[cfg(test)]
use crate::{test_parse_and_check_fail, test_parse_and_compare_ok};

#[test]
fn test_ok_simple_defs() {
    test_parse_and_compare_ok!("const FOO : int = 1234;", constdef);
    test_parse_and_compare_ok!("const FOO : bool = true;", constdef);
    test_parse_and_compare_ok!("const foo : int = 1234;", constdef);
    test_parse_and_compare_ok!("const FOO : int = BAR;", constdef);
    test_parse_and_compare_ok!(
        "const FOO : addr = 0x1200;",
        constdef,
        "const FOO : addr = 4608;"
    );
}

#[test]
fn test_ok_expr() {
    test_parse_and_compare_ok!(
        "const FOO : int = 1+2;",
        constdef,
        "const FOO : int = 1 + 2;"
    );

    test_parse_and_compare_ok!(
        "const FOO : int = BAR+2;",
        constdef,
        "const FOO : int = BAR + 2;"
    );
}

#[test]
fn test_ok_type_mismatch() {
    // wrong type, but should parse
    test_parse_and_compare_ok!("const FOO : size = true;", constdef);
    test_parse_and_compare_ok!("const FOO : addr = true;", constdef);
    test_parse_and_compare_ok!(
        "const FOO : bool = 0x123;",
        constdef,
        "const FOO : bool = 291;"
    );
}

#[test]
fn test_fail_no_semicolon() {
    // no semicolon at the end
    test_parse_and_check_fail!("const FOO : int = 1234 asdf", constdef);
    test_parse_and_check_fail!("const FOO : int = 1234 asdf;", constdef);
}

#[test]
fn test_fail_types_keyword() {
    test_parse_and_check_fail!("const FOO : int = int;", constdef);
}

#[test]
fn test_fail_no_type() {
    // no type
    let content = "const FOO  = true;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(constdef(ts).is_err());
}
