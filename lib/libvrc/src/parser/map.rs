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
use crate::parser::expression::{expr, range_expr};
use crate::parser::terminals::{
    assign, at, comma, dotdot, ident, kw_for, kw_in, kw_map, lbrace, lbrack, num, rbrace, rbrack,
    semicolon,
};
use crate::token::TokenStream;

use nom::branch::alt;
use nom::combinator::{cut, opt};
use nom::multi::{separated_list0, separated_list1};
use nom::sequence::{delimited, pair, preceded, tuple};

// Parses Map Statements
pub fn parse_map(input: TokenStream) -> IResult<TokenStream, Map> {
    let (i1, _) = kw_map(input.clone())?;
    let (i2, entries) = cut(delimited(
        pair(assign, lbrack),
        alt((parse_explicit_map_body, parse_list_comprehension_map_body)),
        pair(rbrack, semicolon),
    ))(i1)?;
    let pos = input.expand_until(&i2);
    Ok((i2, Map { entries, pos }))
}

// Parses explicit map body of the type:
// UnitName(Expr), ..., UnitName(Expr)
// Optionally also parses: UnitName(Expr) @ Number
fn parse_explicit_map_body(input: TokenStream) -> IResult<TokenStream, Vec<MapEntry>> {
    let (i1, map_body): (TokenStream, Vec<(String, Vec<Expr>, Option<Expr>)>) = separated_list1(
        comma,
        tuple((
            ident,
            delimited(lparen, separated_list0(comma, expr), rparen),
            opt(preceded(at, expr)),
        )),
    )(input)?;
    let mut map_entries: Vec<MapEntry> = vec![];
    for (u, p, o) in map_body {
        map_entries.push(MapEntry {
            range: None,
            unit_name: u,
            unit_params: p,
            offset: o,
            ..Default::default()
        });
    }
    Ok((i1, map_entries))
}

// Parses List Comprehension map bodies of the type:
// Optional(Range) UnitName(ident) Optional(@ Number) for ident in Number..Number
fn parse_list_comprehension_map_body(input: TokenStream) -> IResult<TokenStream, Vec<MapEntry>> {
    let (i1, (unit_range, unit_name, unit_params, offset)) = tuple((
        opt(range_expr),
        ident,
        delimited(lparen, separated_list0(comma, expr), rparen),
        opt(preceded(at, expr)),
    ))(input)?;
    let (_i2, (list_itterator, (lower, _, upper))) = tuple((
        preceded(kw_for, ident),
        preceded(kw_in, tuple((num, dotdot, num))),
    ))(i1)?;
    let mut map_entries: Vec<MapEntry> = vec![];
    for i in lower..=upper {
        map_entries.push(MapEntry {
            range: unit_range.clone(),
            unit_name: unit_name.clone(),
            unit_params: unit_params.clone(),
            offset: offset.clone(),
            iteration: Some((list_itterator.clone(), i)),
        })
    }
    Ok((_i2, map_entries))
}


#[cfg(test)]
use crate::ast::BitSlice;
#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::nom::Slice;

#[test]
fn test_map_simple() {
    let content = "map = [UnitA(), UnitB()];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    let res = parse_map(ts);
    assert!(res.is_ok());

    let content = "map = [UnitA() for i in 0..512];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    let res = parse_map(ts);
    println!("{:?}", res);
    assert!(res.is_ok());
}