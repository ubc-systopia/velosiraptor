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

use crate::ast::Map;
use crate::error::IResult;
use crate::parser::expression::{expr, range_expr};
use crate::parser::terminals::{
    assign, comma, ident, kw_for, kw_map, lbrace, lbrack, rbrace, rbrack, semicolon,
};
use crate::token::TokenStream;
use nom::branch::alt;
use nom::combinator::cut;
use nom::multi::separated_list1;
use nom::sequence::{delimited, pair, preceded, tuple};

// Encompases all the different cases of Map parsing.
fn parse_map(input: TokenStream) -> IResult<TokenStream, Map> {
    alt((
        parse_explicit_map,
        parse_simple_list_comprehension,
        parse_address_range_list_comprehension,
    ))(input)
}

// Parses explicit map lists of the type:
// map = [ UnitName(ident + offset), ..., UnitName(ident + offset) ];
fn parse_explicit_map(input: TokenStream) -> IResult<TokenStream, Map> {
    let (i1, _) = kw_map(input.clone())?;
    let map_body_parser = delimited(
        lbrack,
        // UnitName(ident + offset), UnitName(ident + offset)
        separated_list1(comma, pair(ident, delimited(lbrace, expr, rbrace))),
        rbrack,
    );
    let (i2, units) = cut(delimited(assign, map_body_parser, semicolon))(i1)?;
    let pos = input.expand_until(&i2);
    Ok((
        i2,
        Map {
            // NOTE: length of size is 0 in this case because we won't actually know what they are until
            // we compile the Units which it is constructed from.
            sizes: vec![],
            units,
            pos,
        },
    ))
}

// Parses List Comprehensin that split the addres space equally amongst them:
// These should look like:
// map = [ UnitName(Expr) for ident in x..y ]
fn parse_simple_list_comprehension(input: TokenStream) -> IResult<TokenStream, Map> {
    let (i1, _) = kw_map(input.clone())?;

    // TODO: map_body_parser
    let map_body_parser = delimited(
        lbrack,
        tuple((
            ident,
            delimited(lbrace, expr, rbrace),
            preceded(kw_for, ident),
            preceded(kw_for, range_expr),
        )),
        rbrack,
    );

    let (i2, (unitname, unit_arg, itter_var, range)) =
        cut(delimited(assign, map_body_parser, semicolon))(i1)?;
    let pos = input.expand_until(&i2);
    Ok((
        i2,
        Map {
            sizes: vec![],
            units: vec![],
            pos,
        },
    ))
}

// Parses List Comprehension that explicitly lists the address
fn parse_address_range_list_comprehension(_input: TokenStream) -> IResult<TokenStream, Map> {
    todo!()
}
