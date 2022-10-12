// VelosiParser -- Parser for the VelosiRaptor specification language
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
    sequence::{delimited, preceded, tuple},
};

// the used library-internal functionaltity
use crate::error::IResult;
use crate::parser::{
    constdef,
    interface::interface,
    // flags, interface, state
    // map::parse_map,
    method::method,
    param::parameter,
    state,
    terminals::{
        assign, colon, comma, ident, kw_flags, kw_inbitwidth, kw_outbitwidth, kw_segment,
        kw_staticmap, lbrace, lparen, num, rbrace, rparen, semicolon,
    },
};
use crate::parsetree::{
    VelosiParseTreeConstDef, VelosiParseTreeFlag, VelosiParseTreeFlags, VelosiParseTreeParam,
    VelosiParseTreeUnit, VelosiParseTreeUnitDef, VelosiParseTreeUnitNode,
};
use crate::VelosiTokenStream;

/// parses the unit parameters
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a vector of [VelosiParseTreeParam] and the remaining [VelosiTokenStream]
/// if the parser succeeded, or an error wrapping the input position if the parser failed.
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
fn param_clause(input: VelosiTokenStream) -> IResult<VelosiTokenStream, Vec<VelosiParseTreeParam>> {
    let params = delimited(lparen, separated_list0(comma, parameter), cut(rparen));
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
/// Result type wrapping a [String] and the remaining [VelosiTokenStream] if the parser succeeded,
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
fn derived_clause(input: VelosiTokenStream) -> IResult<VelosiTokenStream, String> {
    preceded(colon, cut(ident))(input)
}

/// type definition for the unit header parser
type UnitHeader = (String, Vec<VelosiParseTreeParam>, Option<String>);

/// parses the unit header
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [UnitHeader] and the remaining [VelosiTokenStream] if the parser succeeded,
/// or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// `UNIT_HEADER := IDENTIFIER (LPAREN PARAM_CLAUSE RPAREN)? DERIVED_CLAUSE?`
///
/// # Example
///
///  * `Foo (bar: baz, foo: bar) : FooBar`
fn unit_header(input: VelosiTokenStream) -> IResult<VelosiTokenStream, UnitHeader> {
    tuple((cut(ident), param_clause, opt(derived_clause)))(input)
}

/// parses the input bitwidth clause of the unit
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [u64] and the remaining [VelosiTokenStream] if the parser succeeded,
/// or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// `INBITWIDTH_CLAUSE := KW_INBITWIDTH ASSIGN NUM SEMICOLON`
///
/// # Example
///
///  * `inbitwidth = 32;`
fn inbitwidth_clause(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();
    let (i1, _) = kw_inbitwidth(input)?;
    let (i2, n) = cut(delimited(assign, num, semicolon))(i1)?;

    pos.span_until_start(&i2);
    Ok((i2, VelosiParseTreeUnitNode::OutBitWidth(n, pos)))
}

/// parses the output bitwidth clause of the unit
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [u64] and the remaining [VelosiTokenStream] if the parser succeeded,
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
fn outbitwidth_clause(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();
    let (i1, _) = kw_outbitwidth(input)?;
    let (i2, n) = cut(delimited(assign, num, semicolon))(i1)?;

    pos.span_until_start(&i2);
    Ok((i2, VelosiParseTreeUnitNode::OutBitWidth(n, pos)))
}

/// parses a single flat, currently just an identifier
fn flag(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeFlag> {
    let mut pos = input.clone();
    let (i, n) = ident(input)?;
    pos.span_until_start(&i);
    Ok((i, VelosiParseTreeFlag::new(n, pos)))
}

////
fn flags_clause(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();
    // parse the `const` keyword, return otherwise
    let (i1, _) = kw_flags(input.clone())?;

    let flagsblock = delimited(
        lbrace,
        separated_list0(comma, flag),
        tuple((opt(comma), rbrace)),
    );

    let (i2, flags) = cut(delimited(assign, flagsblock, semicolon))(i1)?;
    pos.span_until_start(&i2);

    Ok((
        i2,
        VelosiParseTreeUnitNode::Flags(VelosiParseTreeFlags::new(flags, pos)),
    ))
}

/// parses the unit body
///
/// # Arguments
///
/// # Return Value
///
/// # Grammar
///
/// `UNIT_BODY := (STATE_CLAUSE | INTERFACE_CLAUSE | METHOD_CLAUSE | CONSTDEF_CLAUSE |
///                FLAGS_CLAUSE | STATICMAP_CLAUSE)*`
///
fn unit_body(input: VelosiTokenStream) -> IResult<VelosiTokenStream, Vec<VelosiParseTreeUnitNode>> {
    many0(alt((
        inbitwidth_clause,
        outbitwidth_clause,
        method,
        state,
        interface,
        flags_clause,
        map(constdef, |s: VelosiParseTreeConstDef| {
            VelosiParseTreeUnitNode::Const(s)
        }),
    )))(input)
}

/// parses and consumes a segment unit declaration
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [VelosiParseTreeUnit] and the remaining [VelosiTokenStream] if the
/// parser succeeded, or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// UNIT_STATICMAP := KW_SEGMENT UNIT_HEADER LBRACE UNIT_BODY RBRACE
///
fn unit_segment(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnit> {
    let mut pos = input.clone();

    // try to match the segment keyword, if there is no match, return early.
    let (i1, _) = kw_segment(input)?;

    // we've seen the `staticmap` keyword, next there needs to be the unit identifier,
    // followed bby some optional parameters and the derived clause.
    let (i2, (unitname, params, derived)) = cut(unit_header)(i1)?;

    // parse the body within the curly brances
    let (i3, body) = cut(delimited(lbrace, unit_body, rbrace))(i2)?;

    pos.span_until_start(&i3);

    let unitdef = VelosiParseTreeUnitDef::new(unitname, params, derived, body, pos);
    Ok((i3, VelosiParseTreeUnit::Segment(unitdef)))
}

/// parses and consumes a staticmap unit declaration
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [VelosiParseTreeUnit] and the remaining [VelosiTokenStream] if the
/// parser succeeded, or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// UNIT_STATICMAP := KW_STATICMAP UNIT_HEADER LBRACE UNIT_BODY RBRACE
///
fn unit_staticmap(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnit> {
    let mut pos = input.clone();

    // try to match the staticmap keyword, if there is no match, return early.
    let (i1, _) = kw_staticmap(input)?;

    // we've seen the `staticmap` keyword, next there needs to be the unit identifier,
    // followed bby some optional parameters and the derived clause.
    let (i2, (unitname, params, derived)) = cut(unit_header)(i1)?;

    // parse the body within the curly brances
    let (i3, body) = cut(delimited(lbrace, unit_body, rbrace))(i2)?;

    pos.span_until_start(&i3);

    let unitdef = VelosiParseTreeUnitDef::new(unitname, params, derived, body, pos);
    Ok((i3, VelosiParseTreeUnit::StaticMap(unitdef)))
}

/// parses and consumes a unit definition with its state, interface etc.
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [Unit] and the remaining [VelosiTokenStream] if the parser succeeded,
/// or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// UNIT := UNIT_SEGMENT | UNIT_STATICMAP
///
pub fn unit(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnit> {
    alt((unit_segment, unit_staticmap))(input)
}

#[cfg(test)]
//use crate::lexer::Lexer;
#[test]
fn test_ok() {

    // we need some more tests here that also include the unit body, as the
    // parser now requires certain elements to be present.

    // let tokens = Lexer::lex_string("stdio", "segment foo {}").unwrap();
    // let ts = VelosiTokenStream::from_vec(tokens);
    // println!("{:?}", unit_segment(ts.clone()));
    // assert!(unit_segment(ts).is_ok());

    // let tokens = Lexer::lex_string("stdio", "segment foo(base: addr) : bar {}").unwrap();
    // let ts = VelosiTokenStream::from_vec(tokens);
    // assert!(unit_segment(ts).is_ok());

    // let tokens =
    //     Lexer::lex_string("stdio", "segment foo : bar { const foo : int = 32; }").unwrap();
    // let ts = VelosiTokenStream::from_vec(tokens);
    // assert!(unit_segment(ts).is_ok());

    // let tokens = Lexer::lex_string("stdio", "segment foo : bar { size = 33; }").unwrap();
    // let ts = VelosiTokenStream::from_vec(tokens);
    // assert!(unit_segment(ts).is_ok());
}
