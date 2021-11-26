// Velosiraptor Parser
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

// TODO:
//  1. Parse Explicit Lists
//  2. List Comprehension that split the address space equally amongst them.
//  3. List Comprehension with explicit address ranges.

use crate::ast::{Expr, Map, MapEntry};
use crate::error::IResult;
use crate::parser::expression::{expr, expr_list, range_expr};
use crate::parser::terminals::{
    assign, at, comma, dotdot, fatarrow, ident, kw_for, kw_in, kw_staticmap, lbrack, lparen, num,
    rbrack, rparen, semicolon,
};
use crate::token::TokenStream;

use nom::branch::alt;
use nom::combinator::{cut, opt};
use nom::multi::separated_list1;
use nom::sequence::{delimited, pair, preceded, terminated, tuple};

// Parses Map Statements
pub fn parse_map(input: TokenStream) -> IResult<TokenStream, Map> {
    let (i1, _) = kw_staticmap(input.clone())?;
    let (i2, entries) = cut(delimited(
        pair(assign, lbrack),
        alt((list_comprehension, entry_list)),
        pair(rbrack, semicolon),
    ))(i1)?;
    let pos = input.expand_until(&i2);
    Ok((i2, Map { entries, pos }))
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
    let (i1, (src, (dst, args, offset))) = pair(opt(map_src), map_dst)(input)?;

    Ok((
        i1,
        MapEntry {
            range: src,
            unit_name: dst,
            unit_params: args,
            offset,
            iteration: None,
        },
    ))
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

/// parses a list of map entries
///
/// # Grammar
///
/// `ENTRY_LIST := MAP_ELEMENT (COMMA MAP_ELEMENT)*`
///
/// # Example
///
/// - `0..0x1000 => UnitA() @ 0x10, 0x2000..0x3000 => UnitA() @ 0x20`
fn entry_list(input: TokenStream) -> IResult<TokenStream, Vec<MapEntry>> {
    separated_list1(comma, map_element)(input)
}

/// parses a list comprehension of map entries
///
/// # Grammar
///
/// `LIST_COMPREHENSION := MAP_ELEMENT FOR IDENT IN RANGE_EXPR`
///
/// # Example
///
///  - `UnitA() for i in 0..512`
///
fn list_comprehension(input: TokenStream) -> IResult<TokenStream, Vec<MapEntry>> {
    let (i1, elm) = map_element(input)?;

    let (i2, (list_itterator, (lower, _, upper))) = tuple((
        preceded(kw_for, cut(ident)),
        preceded(cut(kw_in), cut(tuple((num, dotdot, num)))),
    ))(i1)?;

    let mut map_entries: Vec<MapEntry> = vec![];
    for i in lower..=upper {
        let mut entry = elm.clone();
        entry.iteration = Some((list_itterator.clone(), i));
        map_entries.push(entry);
    }
    Ok((i2, map_entries))
}

#[cfg(test)]
use crate::ast::BitSlice;
#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::nom::Slice;

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
