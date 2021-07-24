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
use crate::parser::bitslice::bitslice;
use crate::parser::terminals::{comma, ident, lbrace, lbrack, num, rbrace, rbrack};
use crate::token::TokenStream;
use crate::error::IResult;

// the used nom componets
use nom::error::ErrorKind;
use nom::multi::separated_list1;
use nom::sequence::{delimited, tuple};

/// Parses a field definition
///
///
///  ident [ident, num, num] { FIELDS };
///
pub fn field(input: TokenStream) -> IResult<TokenStream, Field> {
    // record the position of the field
    let pos = input.input_sourcepos();

    // we first start of with an identifier,
    let (i1, name) = match ident(input) {
        Ok((rem, s)) => (rem, s),
        Err(x) => return Err(x),
    };

    // next we have the `[ident, num, num]`
    let mut fieldhdr = delimited(lbrack, tuple((ident, comma, num, comma, num)), rbrack);
    let (i2, (base, _, offset, _, length)) = fieldhdr(i1.clone())?;

    // we match two numbers and an identifier
    let (rem, layout) = delimited(lbrace, separated_list1(comma, bitslice), rbrace)(i2.clone())?;
    Ok((
        rem,
        Field {
            name,
            stateref: Some((base, offset)),
            length,
            layout,
            pos,
        },
    ))
}

#[cfg(test)]
use crate::ast::BitSlice;
#[cfg(test)]
use crate::nom::Slice;
#[cfg(test)]
use crate::sourcepos::SourcePos;
#[cfg(test)]
use crate::token::{Token, TokenContent};

#[test]
fn test_ok() {
    let content = "foo [ base, 0, 1 ] { 0 16 foobar }";
    let sp = SourcePos::new("stdio", content);

    let tokens = vec![
        Token::new(TokenContent::Identifier("foo".to_string()), sp.slice(0..3)),
        Token::new(TokenContent::LBracket, sp.slice(0..3)),
        Token::new(TokenContent::Identifier("base".to_string()), sp.slice(0..3)),
        Token::new(TokenContent::Comma, sp.slice(0..3)),
        Token::new(TokenContent::IntLiteral(0), sp.slice(0..3)),
        Token::new(TokenContent::Comma, sp.slice(0..3)),
        Token::new(TokenContent::IntLiteral(32), sp.slice(0..3)),
        Token::new(TokenContent::RBracket, sp.slice(0..3)),
        Token::new(TokenContent::LBrace, sp.slice(0..3)),
        Token::new(TokenContent::IntLiteral(0), sp.slice(0..3)),
        Token::new(TokenContent::IntLiteral(16), sp.slice(0..3)),
        Token::new(
            TokenContent::Identifier("foobar".to_string()),
            sp.slice(0..3),
        ),
        Token::new(TokenContent::RBrace, sp.slice(0..3)),
    ];
    let ts = TokenStream::from_slice(&tokens);
    let fields = BitSlice {
        start: 0,
        end: 16,
        name: "foobar".to_string(),
        pos: ts.slice(9..).input_sourcepos(),
    };
    assert_eq!(
        field(ts.clone()),
        Ok((
            ts.slice(13..),
            Field {
                name: "foo".to_string(),
                stateref: Some(("base".to_string(), 0)),
                length: 32,
                layout: vec![fields],
                pos: ts.input_sourcepos()
            }
        ))
    );
}

#[test]
fn test_err() {
    let content = "foo [ base, 0, 1 ] { }";
    let sp = SourcePos::new("stdio", content);

    let tokens = vec![
        Token::new(TokenContent::Identifier("foo".to_string()), sp.slice(0..3)),
        Token::new(TokenContent::LBracket, sp.slice(0..3)),
        Token::new(TokenContent::Identifier("base".to_string()), sp.slice(0..3)),
        Token::new(TokenContent::Comma, sp.slice(0..3)),
        Token::new(TokenContent::IntLiteral(0), sp.slice(0..3)),
        Token::new(TokenContent::Comma, sp.slice(0..3)),
        Token::new(TokenContent::IntLiteral(32), sp.slice(0..3)),
        Token::new(TokenContent::RBracket, sp.slice(0..3)),
        Token::new(TokenContent::LBrace, sp.slice(0..3)),
        Token::new(TokenContent::RBrace, sp.slice(0..3)),
    ];
    let ts = TokenStream::from_slice(&tokens);
    assert!(field(ts).is_err());
}
