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

//! # VelosiParser: Methods
//!
//! This module contains the parser for method definitions within the unit contexts.

// external dependencies
use nom::{
    branch::alt,
    combinator::{cut, opt},
    multi::{many0, separated_list1},
    sequence::{delimited, preceded, terminated, tuple},
};

// used crate functionality
use crate::error::IResult;
use crate::parser::expr::{expr, quantifier_expr};
use crate::parser::parameter::param_list;
use crate::parser::terminals::{
    comma, hashtag, ident, kw_abstract, kw_ensures, kw_fn, kw_requires, kw_synth, lbrace, lbrack,
    lparen, rarrow, rbrace, rbrack, rparen, semicolon, typeinfo,
};
use crate::parsetree::{
    VelosiParseTreeExpr, VelosiParseTreeMethod, VelosiParseTreeMethodProperty,
    VelosiParseTreeUnitNode,
};
use crate::VelosiTokenStream;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Method Parsing
////////////////////////////////////////////////////////////////////////////////////////////////////

/// parses a method definition
///
/// This function parses a method definition in the unit context. The method's body can refer to
/// the state, but not the interface.
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
/// `METHOD := DECORATOR_LIST KW_ABSTRACT? KW_SYNTH? KW_FN IDENT LPAREN ARGLIST RPAREN RARROW TYPE REQUIRES* ENSURES* METHOD_BODY`
///
/// # Examples
///
///  * `fn foo() -> addr`
///  * `fn foo() -> addr { 0 }`
///
pub fn method(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    // parse the decorator #[foo]
    let (i0, props) = opt(decorator_list)(input)?;

    // parse and consume fn keyword
    let (i1, (abs, synth, _)) = if props.is_some() {
        cut(tuple((opt(kw_abstract), opt(kw_synth), kw_fn)))(i0)
    } else {
        tuple((opt(kw_abstract), opt(kw_synth), kw_fn))(i0)
    }?;

    // get the method identifier, fail if there is not an identifier
    let (i2, name) = cut(ident)(i1)?;

    // arguments `LPAREN ARGLIST RPAREN`, fail on missing parenstheses
    let (i3, params) = cut(param_list)(i2)?;

    // get the return type `-> Type`, fail if there is no arrow, or type info
    let (i4, rettype) = opt(preceded(rarrow, cut(typeinfo)))(i3)?;

    // get the ensures / requires clauses
    //let (i5, (requires, ensures)) = tuple((many0(requires_clause), many0(ensures_clause)))(i4)?;
    let (i5, requires) = many0(requires_clause)(i4)?;
    let (i6, ensures) = many0(ensures_clause)(i5)?;

    // try to parse the method body
    let (i7, (body, _)) = tuple((opt(method_body), opt(semicolon)))(i6)?;

    // create the token stream covering the entire method def
    pos.span_until_start(&i7);

    let method = VelosiParseTreeMethod {
        name,
        properties: props.unwrap_or_default(),
        is_abstract: abs.is_some(),
        is_synth: synth.is_some(),
        params,
        rettype,
        requires,
        ensures,
        body,
        pos,
    };
    Ok((i7, VelosiParseTreeUnitNode::Method(method)))
}

/// Parses a require clause of a method
///
/// This adds a pre-condition to the function/method
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized requires clause as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `REQUIRE := KW_REQUIRES BOOL_EXPR;`
///
/// # Examples
///
/// * `requires arg > 0`
///
pub fn requires_clause(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let (i1, _) = kw_requires(input)?;
    cut(terminated(alt((quantifier_expr, expr)), opt(semicolon)))(i1)
}

/// Parses a ensures clause
///
/// This adds a post-condition to the function/method.
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized ensures clause as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `ENSURES := KW_ENSURES BOOL_EXPR;`
///
/// # Examples
///
///  * `ensures ret < 5`
///
pub fn ensures_clause(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let (i1, _) = kw_ensures(input)?;
    cut(terminated(alt((quantifier_expr, expr)), opt(semicolon)))(i1)
}

/// parses the method body
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized method body as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `FN_BODY := LPAREN EXPR RPAREN`
///
/// # Examples
///
/// * `{ 0 }`
///
fn method_body(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    delimited(lbrace, cut(expr), cut(rbrace))(input)
}

/// parses a decorator/property list of a method
///
/// This function parses a function decorator/property
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized decorator list as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `DECORATOR := KW_HASHTAG RBRAK DECORATOR_ELEMENT RBRAK`
///
/// # Example
///
/// * `#[foo]`
///
fn decorator_list(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, Vec<VelosiParseTreeMethodProperty>> {
    let (i1, _) = hashtag(input)?;

    // [ ident ]
    let (i2, decorators) = cut(delimited(
        lbrack,
        separated_list1(comma, decorator_element),
        rbrack,
    ))(i1)?;

    Ok((i2, decorators))
}

/// parses a decorator/property element
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized decorator/property as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `DECORATOR_ELEMENT := IDENT (LPAREN IDENT RPAREN)?`
///
/// # Examples
///
///  * `foo`
///  * `bar(a)`
///
///
fn decorator_element(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeMethodProperty> {
    let (i1, name) = ident(input)?;
    let (i2, arg) = opt(delimited(lparen, cut(ident), cut(rparen)))(i1)?;
    Ok((i2, (name, arg)))
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
use velosilexer::VelosiLexer;

#[cfg(test)]
use crate::{test_parse_and_check_fail, test_parse_and_check_ok};

#[test]
fn test_decorator_ok() {
    test_parse_and_check_ok!("foo", decorator_element);
    test_parse_and_check_ok!("foo(bar)", decorator_element);
}

#[test]
fn test_decorator_fail() {
    test_parse_and_check_fail!("foo(bar, baz)", decorator_element);
    test_parse_and_check_fail!("foo[bar, baz]", decorator_element);
}

#[test]
fn test_decorator_list_ok() {
    test_parse_and_check_ok!("#[foo]", decorator_list);
    test_parse_and_check_ok!("#[foo(bar)]", decorator_list);
    test_parse_and_check_ok!("#[foo(bar), baz]", decorator_list);
}

#[test]
fn test_decorator_list_fail() {
    test_parse_and_check_fail!("#[]", decorator_list);
    test_parse_and_check_fail!("#[foo(bar),]", decorator_list);
    test_parse_and_check_fail!("#[foo(bar) baz]", decorator_list);
}

#[test]
fn test_method_body_ok() {
    // empty body
    test_parse_and_check_ok!("{ 3 }", method_body);
}

#[test]
fn test_method_body_fail() {
    test_parse_and_check_fail!("{}", method_body);
    test_parse_and_check_fail!("{ 3 ; 4}", method_body);
}

#[test]
fn test_ensures_ok() {
    // without semicolon
    test_parse_and_check_ok!("ensures true", ensures_clause);
    // with semicolon
    test_parse_and_check_ok!("ensures true;", ensures_clause);
    test_parse_and_check_ok!("ensures p > 0;", ensures_clause);
    // doesn't make sense, but should parse
    test_parse_and_check_ok!("ensures 3;", ensures_clause);
}

#[test]
fn test_ensures_fail() {
    // wrong terminator
    test_parse_and_check_fail!("ensures true,", ensures_clause);
}

#[test]
fn test_requires_ok() {
    // without semicolon
    test_parse_and_check_ok!("requires true", requires_clause);
    // with semicolon
    test_parse_and_check_ok!("requires true;", requires_clause);
    test_parse_and_check_ok!("requires p > 0;", requires_clause);
    // doesn't make sense, but should parse
    test_parse_and_check_ok!("requires 3;", requires_clause);
}

#[test]
fn test_requires_fail() {
    // wrong terminator
    test_parse_and_check_fail!("requires true,", requires_clause);
}

#[test]
fn test_method_ok() {
    // see the `tests` directory
}
