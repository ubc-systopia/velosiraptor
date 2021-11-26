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

//! State Field parsing

// lexer, parser terminals and ast
use crate::ast::Field;
use crate::error::IResult;
use crate::parser::bitslice::bitslice_block;
use crate::parser::terminals::{comma, ident, lbrace, lbrack, num, rbrace, rbrack, semicolon};
use crate::token::TokenStream;

// the used nom componets
use nom::{
    combinator::{cut, opt},
    multi::many1,
    sequence::{delimited, pair, terminated},
};

/// parses a block of memory fields
///
/// # Grammar
///
/// MEM_FIELD_BLOCK := "{" MEM_FIELD+ "}"
///
/// # Results
///
///  * OK:      the parser could successfully recognize the memory field blcok
///  * Error:   the parser could not recognize the memory field block
///  * Failure: the parser recognized the memory field block, but it did not properly parse
///
/// # Examples
///
///  - `{ foo [base, 0, 4]; foo [base, 4, 8]; }`
///
pub fn mem_field_block(input: TokenStream) -> IResult<TokenStream, Vec<Field>> {
    delimited(lbrace, many1(mem_field), cut(rbrace))(input)
}

/// parses a block of register fields
///
/// # Grammar
///
/// REG_FIELD_BLOCK := "{" REG_FIELD+ "}"
///
/// # Results
///
///  * OK:      the parser could successfully recognize the register field blcok
///  * Error:   the parser could not recognize the register field block
///  * Failure: the parser recognized the register field block, but it did not properly parse
///
/// # Examples
///
///  - `{ foo [4]; foo [8]; }`
///
pub fn reg_field_block(input: TokenStream) -> IResult<TokenStream, Vec<Field>> {
    delimited(lbrace, many1(reg_field), cut(rbrace))(input)
}

/// parses a register field definition
///
/// # Grammar
///
/// MEM_FIELD := IDENT MEM_FIELD_PARAMS BITSLICE_BLOCK? ";"
///
/// # Results
///
///  * OK:      the parser could successfully recognize the interface field
///  * Error:   the parser could not recognize  the interface field definition keyword
///  * Failure: the parser recognized the interface field, but it did not properly parse
///
/// # Examples
///
/// `foo [8] {};
///
pub fn mem_field(input: TokenStream) -> IResult<TokenStream, Field> {
    // we first start of with an identifier,
    let (i1, (name, (stateref, length))) = pair(ident, cut(mem_field_params))(input.clone())?;

    // now recognize the optional bitslices, and the semicolon.
    let (rem, bitslices) = terminated(opt(bitslice_block), cut(semicolon))(i1)?;

    // calculate the position of the bitslice
    let pos = input.expand_until(&rem);

    Ok((
        rem,
        Field {
            name,
            stateref: Some(stateref),
            length,
            layout: bitslices.unwrap_or_default(),
            pos,
        },
    ))
}

/// parses a register field definition
///
/// # Grammar
///
/// REG_FIELD := IDENT REG_FIELD_PARAMS BITSLICE_BLOCK? ";"
///
/// # Results
///
///  * OK:      the parser could successfully recognize the interface field
///  * Error:   the parser could not recognize  the interface field definition keyword
///  * Failure: the parser recognized the interface field, but it did not properly parse
///
/// # Examples
///
/// `foo [8] {};
pub fn reg_field(input: TokenStream) -> IResult<TokenStream, Field> {
    // we first start of with an identifier,
    let (i1, (name, length)) = pair(ident, cut(reg_field_params))(input.clone())?;

    // now recognize the optional bitslices, and the semicolon.
    let (rem, bitslices) = terminated(opt(bitslice_block), cut(semicolon))(i1)?;

    // calculate the position of the bitslice
    let pos = input.expand_until(&rem);

    Ok((
        rem,
        Field {
            name,
            stateref: None,
            length,
            layout: bitslices.unwrap_or_default(),
            pos,
        },
    ))
}

/// parses register field parameters
///
/// This parser recognizes field parameters that define the size of the field
///
/// # Grammar
///
/// FIELD_PARAMS := LBRACK NUM RBRACK
///
/// # Results
///
///  * OK:      the parser could successfully recognize the interface field
///  * Error:   the parser could not recognize  the interface field definition keyword
///  * Failure: the parser recognized the interface field, but it did not properly parse
///
/// # Examples
///
///  - width: `[8]`
///
pub fn reg_field_params(input: TokenStream) -> IResult<TokenStream, u64> {
    delimited(lbrack, num, rbrack)(input)
}

/// parses memory field parameters
///
/// This parser recognizes field parameters that define the size of the field,
/// and the memory location
///
/// # Grammar
///
/// FIELD_PARAMS := LBRACK IDENT, NUM, NUM RBRACK
///
/// # Results
///
///  * OK:      the parser could successfully recognize the interface field
///  * Error:   the parser could not recognize  the interface field definition keyword
///  * Failure: the parser recognized the interface field, but it did not properly parse
///
/// # Examples
///
///  - base, offset, width: [base, 4, 4]
///
pub fn mem_field_params(input: TokenStream) -> IResult<TokenStream, ((String, u64), u64)> {
    delimited(lbrack, pair(base_offset_parser, num), rbrack)(input)
}

/// parses a base-offset pair
///
/// This parser recognizes a base-offset pair, which is used to define the memory location
/// of a field
///
/// # Grammar
///
/// `BASE_OFFSET := IDENT, NUM`
///
/// # Results
///
///  * OK:      the parser could successfully recognize the base-offset pair
///  * Error:   the parser could not recognize the base-offset pair definition keyword
///  * Failure: the parser recognized the base-offset pair, but it did not properly parse
///
/// # Examples
///
///  - base, 4
///  - base, 16
///
fn base_offset_parser(input: TokenStream) -> IResult<TokenStream, (String, u64)> {
    pair(terminated(ident, cut(comma)), cut(terminated(num, comma)))(input)
}

#[cfg(test)]
use crate::ast::BitSlice;
#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::nom::Slice;

#[test]
fn test_ok() {
    let content = "foo [ base, 0, 1 ] { 0 15 foobar; };";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());

    let fields = BitSlice {
        start: 0,
        end: 15,
        name: "foobar".to_string(),
        pos: ts.slice(9..13),
    };
    assert_eq!(
        mem_field(ts.clone()),
        Ok((
            ts.slice(15..),
            Field {
                name: "foo".to_string(),
                stateref: Some(("base".to_string(), 0)),
                length: 1,
                layout: vec![fields],
                pos: ts.slice(0..15)
            }
        ))
    );

    let content = "foo [ base, 0, 1 ] { 0 16 foobar; };";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(mem_field(ts).is_ok());

    let content = "foo [ base, 0, 1 ] {  0 15 foobar; 16 31 foobar2; };";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(mem_field(ts).is_ok());

    let content = "foo [ 1 ] { 0 16 foobar; };";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(reg_field(ts).is_ok());

    let content = "foo [ base, 0, 1 ];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(mem_field(ts).is_ok());

    let content = "foo [ 1 ];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(reg_field(ts).is_ok());
}

#[test]
fn test_err() {
    // no semicolon in the end
    let content = "foo [ base, 0, 1 ] { 0 15 foobar, 16 31 foobar2 }";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(mem_field(ts).is_err());

    // no semicolon in the end
    let content = "foo [ base, 0, 1 ]";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(mem_field(ts).is_err());

    // incomplete base definition
    let content = "foo [ base, 1 ] { 0 16 foobar }";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(mem_field(ts).is_err());

    // incomplete base definition
    let content = "foo [ 1, 1 ] { 0 16 foobar }";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(mem_field(ts).is_err());

    // incomplete base definition
    let content = "foo [ 1, 1 ] { 0 16 foobar }";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(mem_field(ts).is_err());

    // wrong separator
    let content = "foo [ 1, 1 ] { 0 16 foobar; 0 16 foobar }";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(mem_field(ts).is_err());

    // missing header
    let content = "foo { 0 16 foobar } ";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(mem_field(ts).is_err());

    // empty bit slice
    let content = "foo [ base, 0, 1 ] { };";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(reg_field(ts).is_err());
}
