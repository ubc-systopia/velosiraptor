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

// TODO:
//  1. Parse Explicit Lists
//  2. List Comprehension that split the address space equally amongst them.
//  3. List Comprehension with explicit address ranges.

use crate::error::IResult;
use crate::parser::expr::{expr, fn_call_expr, range_expr};
use crate::parser::terminals::{
    assign, at, comma, fatarrow, ident, kw_for, kw_in, kw_staticmap, lbrack, rbrack, semicolon,
};
use crate::parsetree::{
    VelosiParseTreeExpr, VelosiParseTreeMap, VelosiParseTreeMapElement, VelosiParseTreeMapExplicit,
    VelosiParseTreeMapListComp, VelosiParseTreeUnitNode,
};
use crate::VelosiTokenStream;

use nom::{
    branch::alt,
    combinator::{cut, opt},
    multi::separated_list0,
    sequence::{delimited, pair, preceded, terminated, tuple},
};

/// Parses a map statement
///
/// # Grammar
///
/// MAP := KW_MAP ASSIGN LBRACK (LISTCOMPREHENSIONMAP | EXPLICITMAP) RBRACK
///
/// # Example
///
///  - `map = [UnitA(), UnitB()]`
///  - `map = [UnitA(x) for x in 1..2]`
///
pub fn staticmap(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let (i1, _) = kw_staticmap(input)?;
    let (i2, m) = cut(delimited(
        assign,
        alt((explicitmap, listcomprehensionmap)),
        semicolon,
    ))(i1)?;

    Ok((i2, VelosiParseTreeUnitNode::Map(m)))
}

/// Parses the body of an explicit map list
///
/// # Grammar
///
/// EXPLICITMAP :=  [ MAP_ELEMENT (, MAP_ELEMENT)* ]
///
/// # Example
///
///  - `UnitA(), UnitB()`
///
fn explicitmap(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeMap> {
    let mut pos = input.clone();
    let (i1, elms) = delimited(
        lbrack,
        separated_list0(comma, map_element),
        rbrack, // can't use cut here
    )(input)?;

    pos.span_until_start(&i1);

    Ok((
        i1,
        VelosiParseTreeMap::Explicit(VelosiParseTreeMapExplicit::new(elms, pos)),
    ))
}

/// Parses the body of a list comprehension map
///
/// # Grammar
///
/// LISTCOMPREHENSIONMAP :=  MAP_ELEMENT KW_FOR IDENT KW_IN RANGE_EXPR
///
/// # Example
///
///  - `[UnitA(x) for x in 1..2]`
///
fn listcomprehensionmap(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeMap> {
    let mut pos = input.clone();

    let (i1, (elm, id, expr)) = delimited(
        lbrack,
        tuple((
            map_element,
            delimited(kw_for, cut(ident), cut(kw_in)),
            cut(range_expr),
        )),
        rbrack,
    )(input)?;

    pos.span_until_start(&i1);

    let map = VelosiParseTreeMapListComp::new(elm, id, expr, pos);
    Ok((i1, VelosiParseTreeMap::ListComp(map)))
}

/// parses a map elemenet
///
/// # Grammar
///
/// MAP_ELEMENT := MAP_SRC? MAP_DST
///
/// # Example
///
///  - `UnitA()`
///  - `UnitA(base)
///  - `0..0x1000 => UnitA()`
///  - `0..0x1000 => UnitA() @ 0x10`
fn map_element(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeMapElement> {
    let mut pos = input.clone();

    let (i1, (src, (dst, offset))) = pair(opt(map_src), map_dst)(input)?;

    pos.span_until_start(&i1);
    Ok((i1, VelosiParseTreeMapElement::new(src, dst, offset, pos)))
}

/// parses a map source description
///
/// # Grammar
///
/// MAP_SRC := RANGE_EXPR RARROW
///
/// # Example
///
///  - `0..0x1000 =>`
fn map_src(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    terminated(range_expr, cut(fatarrow))(input)
}

/// parses the destination of a map element
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
) -> IResult<VelosiTokenStream, (VelosiParseTreeExpr, Option<VelosiParseTreeExpr>)> {
    let (i1, cons) = fn_call_expr(input)?;
    // get the offset
    let (i2, offset) = opt(preceded(at, expr))(i1)?;

    Ok((i2, (cons, offset)))
}

#[cfg(test)]
use velosilexer::VelosiLexer;

#[test]
fn test_map_simple() {
    let content = "staticmap = [UnitA(), UnitB()];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());

    let content = "staticmap = [UnitA()];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());

    let content = "staticmap = [UnitA() @ a];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());

    let content = "staticmap = [ 0.. 1 => UnitA()];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());
}

#[test]
fn test_map_comprehension() {
    let content = "staticmap = [UnitA() for i in 0..512];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());

    let content = "staticmap = [UnitA() @ i for i in 0..512];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());

    let content = "staticmap = [0..1 => UnitA() @ i for i in 0..512];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = staticmap(ts);
    assert!(res.is_ok());

    // let content = "staticmap = [0*i..1*i => UnitA() @ i for i in 0..512];";
    // let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    // let res = staticmap(ts);
    // assert!(res.is_ok());
}
