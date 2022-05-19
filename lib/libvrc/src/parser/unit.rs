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
    branch::alt,
    combinator::{cut, map, opt},
    multi::{many0, separated_list0},
    sequence::{delimited, preceded, terminated, tuple},
};

// the used library-internal functionaltity
use crate::ast::{Param, Segment, StaticMap, Unit};
use crate::error::IResult;
use crate::parser::{
    constdef, flags, interface, method, parameter, state,
    terminals::{
        assign, colon, comma, ident, kw_inbitwidth, kw_outbitwidth, kw_segment, kw_staticmap,
        lbrace, lparen, num, rbrace, rparen, semicolon,
    },
};
use crate::token::TokenStream;

/// parses the unit parameters
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a vector of [Param] and the remaining [TokenStream] if the parser succeeded,
/// or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// `PARAM_CLAUSE := COLON IDENTIFIER`
///
/// # Example
///
///  * `: FooBar`
///
/// # Notes
///
///  * None
fn param_clause(input: TokenStream) -> IResult<TokenStream, Vec<Param>> {
    let params = delimited(lparen, separated_list0(comma, cut(parameter)), cut(rparen));
    map(opt(params), |r| r.unwrap_or_default())(input)
}

/// parses the derived clause of a unit
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [String] and the remaining [TokenStream] if the parser succeeded,
/// or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// `DERIVED_CLAUSE := COLON IDENTIFIER`
///
/// # Example
///
///  * `: FooBar`
///
/// # Notes
///
///  * None
fn derived_clause(input: TokenStream) -> IResult<TokenStream, String> {
    preceded(colon, cut(ident))(input)

    // this is a bit a hack, we need to return the derived clause as a string,
    // but `Segment` and `StaticMap` are keywords, not strings, so we need to map the
    // result of the parser to a string here.
    // let smap_seg = map(alt((kw_segment, kw_staticmap)), |s: Keyword| {
    //     format!("{}", s)
    // });

    // match (colon)(input.clone()) {
    //     Ok((i, _)) => ident(i),
    //     Err(_) => {
    //         // print a more helpful error message
    //         let err = VrsError::new_err(
    //             input,
    //             String::from("missing derived from clause for unit"),
    //             Some(String::from("add derived clause here \": Identifier)\"")),
    //         );
    //         Err(Err::Failure(err))
    //     }
    // }
}

/// type definition for the unit header parser
type UnitHeader = (String, Vec<Param>, Option<String>);

/// parses the unit header
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [UnitHeader] and the remaining [TokenStream] if the parser succeeded,
/// or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// `UNIT_HEADER := IDENTIFIER (LPAREN PARAM_CLAUSE RPAREN)? (DERIVED_CLAUSE)?`
///
/// # Example
///
///  * `Foo (bar: baz) : FooBar`
///
/// # Notes
///
///  * None
fn unit_header(input: TokenStream) -> IResult<TokenStream, UnitHeader> {
    tuple((ident, param_clause, opt(derived_clause)))(input)
}

/// parses the input bitwidth clause of the unit
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [u64] and the remaining [TokenStream] if the parser succeeded,
/// or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// `INBITWIDTH_CLAUSE := KW_INBITWIDTH ASSIGN NUM SEMICOLON`
///
/// # Example
///
///  * `inbitwidth = 32;`
///
/// # Notes
///
///  * None
fn inbitwidth_clause(input: TokenStream) -> IResult<TokenStream, u64> {
    let (i1, _) = kw_inbitwidth(input)?;
    cut(delimited(assign, num, semicolon))(i1)
}

/// parses the output bitwidth clause of the unit
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [u64] and the remaining [TokenStream] if the parser succeeded,
/// or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// `OUTBITWIDTH_CLAUSE := KW_OUTBITWIDTH ASSIGN NUM SEMICOLON`
///
/// # Example
///
///  * `outbitwidth = 32;`
///
/// # Notes
///
///  * None
fn outbitwidth_clause(input: TokenStream) -> IResult<TokenStream, u64> {
    let (i1, _) = kw_outbitwidth(input)?;
    cut(delimited(assign, num, semicolon))(i1)
}

/// parses and consumes a segment unit declaration (`segment foo(args) : derived {};`)
fn unit_segment(input: TokenStream) -> IResult<TokenStream, Unit> {
    // try to match the segment keyword, there is no match, return.
    let (i1, _) = kw_segment(input.clone())?;

    // we've seen the `segment` keyword, next there needs to be the unit identifier,
    // followed by some optional parameters and the derived clause.
    let (i2, (unitname, params, derived)) = cut(unit_header)(i1)?;

    // parse the unit body. this is a combination of the following
    let unit_body = tuple((
        many0(constdef),
        opt(inbitwidth_clause),
        opt(outbitwidth_clause),
        opt(flags),
        state,
        interface,
        many0(method),
    ));

    // then we have the unit block, wrapped in curly braces and a ;
    let (i4, (consts, inbitwidth, outbitwidth, _flags, state, interface, methods)) =
        terminated(cut(delimited(lbrace, unit_body, rbrace)), opt(semicolon))(i2)?;

    // build the segment
    let seg = Segment::new(unitname, params, input)
        .set_inbitwidth(inbitwidth)
        .set_outbitwidth(outbitwidth)
        .set_derived(derived)
        .set_state(state)
        .set_interface(interface)
        .add_consts(consts)
        .add_methods(methods)
        .finalize(&i4);

    Ok((i4, Unit::Segment(seg)))
}

/// parses and consumes a staticmap unit declaration
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [Unit] and the remaining [TokenStream] if the parser succeeded,
/// or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// UNIT_STATICMAP := KW_STATICMAP
///
/// # Example
///
/// `staticmap foo(args) : derived {};`
///
/// # Notes
///
/// TODO not sure if we need to have methods in static map declarations
fn unit_staticmap(input: TokenStream) -> IResult<TokenStream, Unit> {
    // try to match the staticmap keyword, if there is no match, return early.
    let (i1, _) = kw_staticmap(input.clone())?;

    // we've seen the `staticmap` keyword, next there needs to be the unit identifier,
    // followed bby some optional parameters and the derived clause.
    let (i2, (unitname, params, derived)) = cut(unit_header)(i1)?;

    // parse the unit body. this is a combination of the following
    let unit_body = tuple((
        many0(constdef),
        opt(inbitwidth_clause),
        opt(outbitwidth_clause),
        parse_map,
        many0(method),
    ));

    // then we have the unit block, wrapped in curly braces and a ;
    let (i4, (consts, inbitwidth, outbitwidth, mapdef, methods)) =
        terminated(cut(delimited(lbrace, unit_body, rbrace)), opt(semicolon))(i2)?;

    // build the static map
    let staticmap = StaticMap::new(unitname, params, input)
        .set_inbitwidth(inbitwidth)
        .set_outbitwidth(outbitwidth)
        .set_derived(derived)
        .set_map(mapdef)
        .add_consts(consts)
        .add_methods(methods)
        .finalize(&i4);

    Ok((i4, Unit::StaticMap(staticmap)))
}

/// parses and consumes a unit definition with its state, interface etc.
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [Unit] and the remaining [TokenStream] if the parser succeeded,
/// or an error wrapping the input position if the parser failed.
///
/// # Notes
///
/// The parser regcognizes the two fundamental unit types:
///
///  * `segment`
///  * `staticmap
///
pub fn unit(input: TokenStream) -> IResult<TokenStream, Unit> {
    alt((unit_segment, unit_staticmap))(input)
}

#[cfg(test)]
use crate::lexer::Lexer;
use crate::parser::map::parse_map;

#[test]
fn test_ok() {
    let tokens = Lexer::lex_string("stdio", "segment foo {};").unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(unit_segment(ts).is_ok());

    let tokens = Lexer::lex_string("stdio", "segment foo(base: addr) : bar {};").unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(unit_segment(ts).is_ok());

    let tokens =
        Lexer::lex_string("stdio", "segment foo : bar { const foo : int = 32; };").unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(unit_segment(ts).is_ok());

    let tokens = Lexer::lex_string("stdio", "segment foo : bar { size = 33; };").unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(unit_segment(ts).is_ok());
}
