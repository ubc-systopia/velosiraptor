// Velosiraptor Parser
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

use crate::ast::{ExplicitMap, Expr, ListComprehensionMap, Map, MapEntry};
use crate::error::IResult;
use crate::parser::expression::{expr, expr_list, range_expr};
use crate::parser::terminals::{
    assign, at, comma, fatarrow, ident, kw_for, kw_in, kw_staticmap, lbrack, lparen, rbrack,
    rparen, semicolon,
};
use crate::token::TokenStream;

use nom::branch::alt;
use nom::combinator::{cut, opt};
use nom::multi::separated_list1;
use nom::sequence::{delimited, pair, preceded, terminated, tuple};

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
pub fn parse_map(input: TokenStream) -> IResult<TokenStream, Map> {
    let (i1, _) = kw_staticmap(input)?;
    let maps = alt((explicitmap, listcomprehensionmap));
    cut(delimited(assign, maps, opt(semicolon)))(i1)
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
fn explicitmap(input: TokenStream) -> IResult<TokenStream, Map> {
    let (i1, elms) = delimited(
        lbrack,
        separated_list1(comma, cut(map_element)),
        rbrack, // can't use cut here
    )(input.clone())?;

    let map = ExplicitMap::new(input).add_entries(elms).finalize(&i1);
    Ok((i1, Map::Explicit(map)))
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
fn listcomprehensionmap(input: TokenStream) -> IResult<TokenStream, Map> {
    let (i1, (elm, id, expr)) = delimited(
        lbrack,
        tuple((
            cut(map_element),
            delimited(kw_for, cut(ident), cut(kw_in)),
            cut(range_expr),
        )),
        cut(rbrack),
    )(input.clone())?;

    let map = ListComprehensionMap::new(elm, id, expr, input).finalize(&i1);
    Ok((i1, Map::ListComprehension(Box::new(map))))
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
fn map_element(input: TokenStream) -> IResult<TokenStream, MapEntry> {
    let (i1, (src, (dst, args, offset))) = pair(opt(map_src), map_dst)(input.clone())?;

    let elm = MapEntry::new(input, dst)
        .set_range(src)
        .set_offset(offset)
        .add_unit_params(args)
        .finalize(&i1);

    Ok((i1, elm))
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
fn map_src(input: TokenStream) -> IResult<TokenStream, Expr> {
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
fn map_dst(input: TokenStream) -> IResult<TokenStream, (String, Vec<Expr>, Option<Expr>)> {
    let (i1, unitname) = ident(input)?;

    // get the unit args
    let (i2, unitargs) = cut(delimited(lparen, expr_list, rparen))(i1)?;

    // get the offset
    let (i3, offset) = opt(preceded(at, expr))(i2)?;

    Ok((i3, (unitname, unitargs, offset)))
}

#[cfg(test)]
use crate::lexer::Lexer;

#[test]
fn test_map_simple() {
    let content = "staticmap = [UnitA(), UnitB()];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    let res = parse_map(ts);
    assert!(res.is_ok());

    let content = "staticmap = [UnitA()];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    let res = parse_map(ts);
    assert!(res.is_ok());

    let content = "staticmap = [UnitA() @ a];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    let res = parse_map(ts);
    assert!(res.is_ok());

    let content = "staticmap = [ 0.. 1 => UnitA()];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    let res = parse_map(ts);
    assert!(res.is_ok());
}

#[test]
fn test_map_comprehension() {
    let content = "staticmap = [UnitA() for i in 0..512];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    let res = parse_map(ts);
    println!("{:?}", res);
    assert!(res.is_ok());

    let content = "staticmap = [UnitA() @ i for i in 0..512];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    let res = parse_map(ts);
    println!("{:?}", res);
    assert!(res.is_ok());

    let content = "staticmap = [0..1 => UnitA() @ i for i in 0..512];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    let res = parse_map(ts);
    println!("{:?}", res);
    assert!(res.is_ok());

    let content = "staticmap = [0*i..1*i => UnitA() @ i for i in 0..512];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    let res = parse_map(ts);
    println!("{:?}", res);
    assert!(res.is_ok());
}
