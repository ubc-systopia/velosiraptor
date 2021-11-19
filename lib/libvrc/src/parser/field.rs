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
use crate::parser::terminals::{comma, ident, lbrack, num, rbrack, semicolon};
use crate::token::TokenStream;

// the used nom componets
use nom::{
    combinator::{cut, opt},
    sequence::{delimited, pair, terminated},
};

/// Parses a field definition
///
/// This parser recognizes a field definition within the state giving a portion of the state
/// a name, so it can be referred to by the interface and functions of the unit.
/// A field must have a name (identifer) and a given size. It may further contain a list
/// of BitSlices that give specific meanings to parts of the field.
///
/// # Syntax
///
///  * Full syntax: `ident [ident, num, num] { FIELDS };`
///  * No fields: `ident [ident, num, num];`
///  * No fields: `ident [ident, num, num] {};
///  * No base/offset: `ident [num];
///
pub fn field(input: TokenStream) -> IResult<TokenStream, Field> {
    // we first start of with an identifier,
    let (i1, name) = ident(input.clone())?;

    // parse the field params
    let (i2, (stateref, length)) = cut(field_params)(i1)?;

    // now recognize the optional bitslices, and the semicolon.
    let (rem, bitslices) = cut(terminated(opt(bitslice_block), semicolon))(i2)?;

    // if there were bitslices parsed unwrap them, otherwise create an empty vector
    let layout = bitslices.unwrap_or_default();

    // calculate the position of the bitslice
    let pos = input.expand_until(&rem);

    Ok((
        rem,
        Field {
            name,
            stateref,
            length,
            layout,
            pos,
        },
    ))
}

/// parses field parameters
///
/// This parser recognizes field parameters that define the size of the field,
/// and the memory location if applicable
///
/// # Grammar
///
/// FIELD_PARAMS := LBRACK [IDENT, NUM, ] NUM
///
/// # Results
///
///  * OK:      the parser could successfully recognize the interface field
///  * Error:   the parser could not recognize  the interface field definition keyword
///  * Failure: the parser recognized the interface field, but it did not properly parse
///
/// # Examples
///
///  - just the width: [8]
///  - base offset, width: [base, 4, 4]
///
pub fn field_params(input: TokenStream) -> IResult<TokenStream, (Option<(String, u64)>, u64)> {
    // define a parser for the base-offset: baseoffsetparser = ident, num,
    let baseoffsetparser = pair(terminated(ident, cut(comma)), cut(terminated(num, comma)));

    // recognize the field header: [baseoffsetparser, num]
    delimited(lbrack, pair(opt(baseoffsetparser), num), rbrack)(input)
}

#[cfg(test)]
use crate::ast::BitSlice;
#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::nom::Slice;

#[test]
fn test_ok() {
    let content = "foo [ base, 0, 1 ] { 0 15 foobar };";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());

    let fields = BitSlice {
        start: 0,
        end: 15,
        name: "foobar".to_string(),
        pos: ts.slice(9..12),
    };
    assert_eq!(
        field(ts.clone()),
        Ok((
            ts.slice(14..),
            Field {
                name: "foo".to_string(),
                stateref: Some(("base".to_string(), 0)),
                length: 1,
                layout: vec![fields],
                pos: ts.slice(0..14)
            }
        ))
    );

    let content = "foo [ base, 0, 1 ] { 0 16 foobar };";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_ok());

    let content = "foo [ base, 0, 1 ] {  0 15 foobar, 16 31 foobar2 };";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_ok());

    let content = "foo [ 1 ] { 0 16 foobar };";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_ok());

    let content = "foo [ base, 0, 1 ] { };";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_ok());

    let content = "foo [ 1 ] { };";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_ok());

    let content = "foo [ base, 0, 1 ];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_ok());

    let content = "foo [ 1 ];";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_ok());
}

#[test]
fn test_err() {
    // no semicolon in the end
    let content = "foo [ base, 0, 1 ] { 0 15 foobar, 16 31 foobar2 }";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_err());

    // no semicolon in the end
    let content = "foo [ base, 0, 1 ]";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_err());

    // incomplete base definition
    let content = "foo [ base, 1 ] { 0 16 foobar }";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_err());

    // incomplete base definition
    let content = "foo [ 1, 1 ] { 0 16 foobar }";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_err());

    // incomplete base definition
    let content = "foo [ 1, 1 ] { 0 16 foobar }";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_err());

    // wrong separator
    let content = "foo [ 1, 1 ] { 0 16 foobar; 0 16 foobar }";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_err());

    // missing header
    let content = "foo { 0 16 foobar } ";
    let ts = TokenStream::from_vec(Lexer::lex_string("stdio", content).unwrap());
    assert!(field(ts).is_err());
}
