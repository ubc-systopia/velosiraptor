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

//! # VelosiParser -- Static Map Parser
//!
//! Thid modules contains the parser for the static map construct representing a fixed
//! address translation scheme. There are two ways to define a static map:
//!  1. Explicitly list all the elements in the map.
//!  2. Using the list comprehension syntax

// used external dependencies
use nom::{
    branch::alt,
    combinator::{cut, opt},
    multi::separated_list1,
    sequence::{delimited, pair, preceded, terminated, tuple},
};

use crate::error::IResult;
use crate::parser::expr::{expr, fn_call_expr, range_expr};
use crate::parser::method::decorator_list;
use crate::parser::terminals::{
    at, comma, fatarrow, ident, kw_for, kw_in, kw_mapdef, lbrack, rbrack,
};
use crate::parsetree::{
    VelosiParseTreeExpr, VelosiParseTreeFnCallExpr, VelosiParseTreeMap, VelosiParseTreeMapElement,
    VelosiParseTreeMapExplicit, VelosiParseTreeMapListComp, VelosiParseTreeRangeExpr,
    VelosiParseTreeUnitNode,
};
use crate::VelosiTokenStream;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Static Map Parsing
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Parses a map statement
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized static map definition as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// STATICMAP := KW_MAP LBRACK (LISTCOMPREHENSIONMAP | EXPLICITMAP) RBRACK
///
/// # Example
///
/// * `maps [ UnitA(), UnitB() ]`
/// * `maps [ UnitA(x) for x in 1..2 ]`
///
pub fn staticmap(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    // parse the decorator #[foo]
    let (i0, props) = opt(decorator_list)(input)?;

    let (i1, _) = kw_mapdef(i0)?;
    let (i2, mut m) = cut(alt((explicitmap, listcomprehensionmap)))(i1)?;

    match &mut m {
        VelosiParseTreeMap::ListComp(l) => {
            l.properties = props.unwrap_or_default();
        }
        VelosiParseTreeMap::Explicit(_) => {}
    }

    Ok((i2, VelosiParseTreeUnitNode::Map(m)))
}

/// Parses the body of an explicit map list
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized explicit static map definition as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `EXPLICITMAP :=  [ MAP_ELEMENT+ ]`
///
/// # Example
///
///  * `[ UnitA(), UnitB() ]`
///
fn explicitmap(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeMap> {
    let mut pos = input.clone();
    let (i1, elms) = delimited(
        lbrack,
        separated_list1(comma, map_element),
        rbrack, // can't use cut here
    )(input)?;

    pos.span_until_start(&i1);

    let map = VelosiParseTreeMapExplicit::new(elms, pos);
    Ok((i1, VelosiParseTreeMap::Explicit(Box::new(map))))
}

/// Parses the body of a list comprehension map
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized list comprehension static map definition as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// LISTCOMPREHENSIONMAP :=  LBRACK MAP_ELEMENT KW_FOR IDENT KW_IN RANGE_EXPR RBRAK
///
/// # Example
///
/// * `[ UnitA(x) for x in 1..2 ]`
///
fn listcomprehensionmap(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeMap> {
    let mut pos = input.clone();

    println!("trying list:comp map");

    let (i1, (elm, id, expr)) = delimited(
        lbrack,
        tuple((
            map_element,
            delimited(kw_for, cut(ident), cut(kw_in)),
            cut(range_expr),
        )),
        rbrack,
    )(input)?;

    println!("trying list:wee");

    pos.span_until_start(&i1);

    let map = VelosiParseTreeMapListComp::new(elm, id, expr, pos);
    Ok((i1, VelosiParseTreeMap::ListComp(Box::new(map))))
}

/// parses a map elemenet
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized static map element as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// MAP_ELEMENT := MAP_SRC? MAP_DST
///
/// # Example
///
/// * `UnitA()`
/// * `UnitA(base)
/// * `0..0x1000 => UnitA()`
/// * `0..0x1000 => UnitA() @ 0x10`
///
fn map_element(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeMapElement> {
    let mut pos = input.clone();

    let (i1, (src, (dst, offset))) = pair(opt(map_src), map_dst)(input)?;

    pos.span_until_start(&i1);
    Ok((i1, VelosiParseTreeMapElement::new(src, dst, offset, pos)))
}

/// parses a map source description
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized source address range of a static map element as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// MAP_SRC := RANGE_EXPR RARROW
///
/// # Example
///
/// * `0..0x1000 =>`
///
fn map_src(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeRangeExpr> {
    terminated(range_expr, cut(fatarrow))(input)
}

/// parses the destination of a map element
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized destination unit of a static map element as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `MAP_ELEMENT := IDENT LPAREN EXPR_LIST RPAREN [AT OFFSET]?
///
/// # Example
///
///  - `UnitA(base) @ 123`
///
fn map_dst(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, (VelosiParseTreeFnCallExpr, Option<VelosiParseTreeExpr>)> {
    let (i1, cons) = fn_call_expr(input)?;
    // get the offset
    let (i2, offset) = opt(preceded(at, expr))(i1)?;

    if let VelosiParseTreeExpr::FnCall(cons) = cons {
        Ok((i2, (cons, offset)))
    } else {
        unreachable!("should always be a function call expression");
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
use velosilexer::VelosiLexer;

#[cfg(test)]
use crate::{test_parse_and_check_fail, test_parse_and_check_ok, test_parse_and_compare_ok};

#[test]
fn test_map_dest_ok() {
    test_parse_and_check_ok!("UnitA()", map_dst);
    test_parse_and_check_ok!("UnitA(foo)", map_dst);
    test_parse_and_check_ok!("UnitA(foo, bar)", map_dst);
    test_parse_and_check_ok!("UnitA(foo, bar * i * 8)", map_dst);
    test_parse_and_check_ok!("UnitA(foo) @ 123", map_dst);
    test_parse_and_check_ok!("UnitA(foo) @ 123 + 432", map_dst);
}

#[test]
fn test_map_dest_fail() {
    test_parse_and_check_fail!("UnitA(foo) -> 123 + 432", map_dst);
    test_parse_and_check_fail!("UnitA @ 123 + 432", map_dst);
}

#[test]
fn test_map_src_ok() {
    test_parse_and_check_ok!("0..0x1000 =>", map_src);
    // TODO: sould have support for this...
    test_parse_and_check_fail!("i * 0x1000..(i+1) * 0x1000 =>", map_src);
}

#[test]
fn test_map_src_fail() {
    test_parse_and_check_fail!("0 =>", map_src);
    test_parse_and_check_fail!("0..10 ->", map_src);
}

#[test]
fn test_map_element_ok() {
    test_parse_and_compare_ok!("UnitA()", map_element);
    test_parse_and_compare_ok!("UnitA(foo)", map_element);
    test_parse_and_compare_ok!("UnitA(foo, bar)", map_element);
    test_parse_and_compare_ok!("UnitA(foo + 123, bar)", map_element);

    test_parse_and_compare_ok!("UnitA() @ 4096", map_element);
    test_parse_and_compare_ok!("UnitA() @ 4096 + (i * 4096)", map_element);

    test_parse_and_compare_ok!("0..4096 => UnitA() @ 4096", map_element);
    test_parse_and_compare_ok!("0..4096 => UnitA() @ 4096 + (i * 4096)", map_element);

    // TODO: sould have support for this...
    test_parse_and_check_fail!("i * 4096..(i+1) * 4096 => UnitA()", map_element);
}

#[test]
fn test_map_element_fail() {
    test_parse_and_check_fail!("0..4096 -> UnitA() @ 4096", map_element);
    test_parse_and_check_fail!("0..4096 -> UnitA @ 4096", map_element);
}

#[test]
fn test_list_comprehension_map_ok() {
    test_parse_and_compare_ok!("[ UnitA() for i in 0..1 ]", listcomprehensionmap);
}

#[test]
fn test_list_comprehension_map_fail() {
    test_parse_and_check_fail!("[ ]", listcomprehensionmap);
}

#[test]
fn test_explicit_map_ok() {
    test_parse_and_compare_ok!("[ UnitA() ]", explicitmap);
}

#[test]
fn test_explicit_map_fail() {
    test_parse_and_check_fail!("[ ]", explicitmap);
}

#[test]
fn test_map_simple() {
    let content = "maps [UnitA(), UnitB()];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());

    let content = "maps [UnitA()];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());

    let content = "maps [UnitA() @ a];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());

    let content = "maps [ 0.. 1 => UnitA()];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());
}

#[test]
fn test_map_comprehension() {
    let content = "maps [UnitA() for i in 0..512];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());

    let content = "maps [UnitA() @ i for i in 0..512];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());

    let content = "maps [0..1 => UnitA() @ i for i in 0..512];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());

    // let content = "staticmap = [0*i..1*i => UnitA() @ i for i in 0..512];";
    // let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    // let res = staticmap(ts);
    // assert!(res.is_ok());
}
