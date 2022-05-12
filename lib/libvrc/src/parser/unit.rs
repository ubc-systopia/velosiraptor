// Velosiraptor Compiler
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

//! Unit Parser
//!
//! Parses a Unit definition including its state, constants etc.

// the used nom functionality
use nom::{
    branch::{permutation, alt},
    combinator::{cut, opt},
    multi::{many0, separated_list0},
    sequence::{delimited, terminated, tuple},
    Err,
};

// the used library-internal functionaltity
use crate::{ast::{Interface, Param, State, Unit, Segment, StaticMap}};
use crate::error::{IResult, VrsError};
use crate::parser::{
    constdef, interface, method, parameter, state,
    terminals::{
        assign, colon, comma, ident, kw_size, lbrace, lparen, num, rbrace, rparen,
        semicolon, kw_staticmap, kw_segment
    },
};
use crate::token::TokenStream;

/// parses and consumes the unit parameters `(foo: bar, bar: baz)`
fn param_clause(input: TokenStream) -> IResult<TokenStream, Vec<Param>> {
    delimited(lparen, separated_list0(comma, cut(parameter)), cut(rparen))(input)
}

/// parses and consumes a size statement in a unit (`size = number`)
fn size_clause(input: TokenStream) -> IResult<TokenStream, u64> {
    let (i1, _) = kw_size(input)?;
    cut(delimited(assign, num, semicolon))(i1)
}

/// parses and consumes the derived clause of a unit: `: IDENTIFIER | KW_SEGMENT | KW_STATICMAP`
fn derived_clause(input: TokenStream) -> IResult<TokenStream, String> {
    // this is a bit a hack, we need to return the derived clause as a string,
    // but `Segment` and `StaticMap` are keywords, not strings, so we need to map the
    // result of the parser to a string here.
    // let smap_seg = map(alt((kw_segment, kw_staticmap)), |s: Keyword| {
    //     format!("{}", s)
    // });

    // let's try to parse the colon indicating the derived clause
    match cut(colon)(input.clone()) {
        Ok((i, _)) => ident(i),
        Err(_) => {
            // print a more helpful error message
            let err = VrsError::new_err(
                input,
                String::from("missing derived from clause for unit"),
                Some(String::from("add derived clause here \": Identifier)\"")),
            );
            Err(Err::Failure(err))
        }
    }
}

pub fn unit(input: TokenStream) -> IResult<TokenStream, Unit> {
    alt((unit_segment, unit_staticmap))(input)
}

/// parses and consumes a segment unit declaration (`segment foo(args) : derived {};`)
fn unit_segment(input: TokenStream) -> IResult<TokenStream, Unit> {
    // try to match the segment keyword, there is no match, return.
    let (i1, _) = kw_segment(input.clone())?;

    // we've seen the `segment` keyword, next there needs to be the unit identifier,
    // followed by some optional parameters and the derived clause.
    let (i2, (unitname, params, derived)) =
        cut(tuple((ident, opt(param_clause), derived_clause)))(i1)?;

    // parse the unit body. this is a combination of the following
    let unit_body = permutation((
        many0(constdef),
        opt(state),
        opt(interface),
        opt(size_clause),
        many0(method),
    ));

    // then we have the unit block, wrapped in curly braces and a ;
    let (i4, (consts, state, interface, size, methods)) =
        cut(terminated(delimited(lbrace, unit_body, rbrace), semicolon))(i2)?;

    let pos = input.expand_until(&i4);

    let segment = Segment {
        name: unitname,
        params: params.unwrap_or_default(),
        derived,
        size,
        consts,
        state: state.unwrap_or(State::None { pos: pos.clone() }),
        interface: interface.unwrap_or(Interface::None {
            pos: TokenStream::empty(),
        }),
        methods,
        map_ops: None,
        unmap_ops: None,
        protect_ops: None,
        pos,
    };

    Ok((i4, Unit::Segment(segment)))
}

/// parses and consumes a staticmap unit declaration (`staticmap foo(args) : derived {};`)
/// 
/// TODO not sure if we need to have methods in static map declarations
fn unit_staticmap(input: TokenStream) -> IResult<TokenStream, Unit> {
    // try to match the staticmap keyword, if there is no match, return early.
    let (i1, _) = kw_staticmap(input.clone())?;

    // we've seen the `staticmap` keyword, next there needs to be the unit identifier,
    // followed bby some optional parameters and the derived clause.
    let (i2, (unitname, params, derived)) = cut(tuple((ident, opt(param_clause), derived_clause)))(i1)?;

    // parse the unit body. this is a combination of the following
    let unit_body = permutation((
        many0(constdef),
        opt(parse_map),
        opt(size_clause),
    ));

    // then we have the unit block, wrapped in curly braces and a ;
    let (i4, (consts, map, size)) = cut(terminated(delimited(lbrace, unit_body, rbrace), semicolon))(i2)?;

    let pos = input.expand_until(&i4);
    let staticmap = StaticMap {
        name: unitname,
        params: params.unwrap_or_default(),
        derived,
        size,
        consts,
        map,
        pos,
    };

    Ok((i4, Unit::StaticMap(staticmap)))
}

// TODO parse map as XOR of unit type parsers.


#[cfg(test)]
use crate::lexer::Lexer;
use crate::parser::map::parse_map;


#[test]
fn test_ok() {
    let tokens = Lexer::lex_string("stdio", "unit foo : Segment {};").unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(unit_segment(ts).is_ok());

    let tokens = Lexer::lex_string("stdio", "unit foo(base: addr) : Segment  {};").unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(unit_segment(ts).is_ok());

    let tokens =
        Lexer::lex_string("stdio", "unit foo : Segment  { const foo : int = 32; };").unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(unit_segment(ts).is_ok());

    let tokens = Lexer::lex_string("stdio", "unit foo : Segment  { size = 33; };").unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(unit_segment(ts).is_ok());
}
