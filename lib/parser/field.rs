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
use crate::lexer::token::TokenStream;
use crate::parser::ast::Field;
use crate::parser::bitslice::bitslice;
use crate::parser::terminals::{comma, ident, lbrace, lbrack, num, rbrace, rbrack};

// the used nom componets
use nom::error::ErrorKind;
use nom::multi::separated_list1;
use nom::sequence::{delimited, tuple};
use nom::{error_position, Err, IResult};

/// Parses a field definition
///
///
///  ident [ident, num, num] { FIELDS };
///
pub fn field(input: TokenStream) -> IResult<TokenStream, Field> {
    // we first start of with an identifier,
    let (i1, name) = match ident(input) {
        Ok((rem, s)) => (rem, s),
        Err(x) => return Err(x),
    };

    println!("{}", i1);

    // next we have the `[ident, num, num]`
    let mut fieldhdr = delimited(lbrack, tuple((ident, comma, num, comma, num)), rbrack);
    let (i2, base, offset, length) = match fieldhdr(i1) {
        Ok((i, (b, _, o, _, l))) => (i, b, o, l),
        Err(e) => {
            // if we have parser failure, indicate this!
            let (i, k) = match e {
                Err::Error(e) => (e.input, e.code),
                _ => (i1, ErrorKind::AlphaNumeric),
            };
            return Err(Err::Failure(error_position!(i, k)));
        }
    };

    println!("{}", i2);

    // we match two numbers and an identifier
    let (rem, entries) = match delimited(lbrace, separated_list1(comma, bitslice), rbrace)(i2) {
        Ok((rem, e)) => (rem, e),
        Err(e) => {
            // if we have parser failure, indicate this!
            let (i, k) = match e {
                Err::Error(e) => (e.input, e.code),
                _ => (i2, ErrorKind::AlphaNumeric),
            };
            return Err(Err::Failure(error_position!(i, k)));
        }
    };

    println!("{}", rem);

    Ok((
        rem,
        Field::new(name, base, offset, length, entries, input.get_pos()),
    ))
}

#[cfg(test)]
use crate::lexer::sourcepos::SourcePos;
#[cfg(test)]
use crate::lexer::token::{Token, TokenContent};
#[cfg(test)]
use crate::nom::Slice;
#[cfg(test)]
use crate::parser::ast::BitSlice;

#[test]
fn test_ok() {
    let tokens = vec![
        Token::new(
            TokenContent::Identifier("foo".to_string()),
            SourcePos::new("stdio", "foo"),
        ),
        Token::new(TokenContent::LBracket, SourcePos::new("stdio", "[")),
        Token::new(
            TokenContent::Identifier("base".to_string()),
            SourcePos::new("stdio", "base"),
        ),
        Token::new(TokenContent::Comma, SourcePos::new("stdio", ",")),
        Token::new(TokenContent::IntLiteral(0), SourcePos::new("stdio", "0")),
        Token::new(TokenContent::Comma, SourcePos::new("stdio", ",")),
        Token::new(TokenContent::IntLiteral(32), SourcePos::new("stdio", "0")),
        Token::new(TokenContent::RBracket, SourcePos::new("stdio", "]")),
        Token::new(TokenContent::LBrace, SourcePos::new("stdio", "{")),
        Token::new(TokenContent::IntLiteral(0), SourcePos::new("stdio", "0")),
        Token::new(
            TokenContent::IntLiteral(16),
            SourcePos::new_at("stdio", "16", 2, 3, 1),
        ),
        Token::new(
            TokenContent::Identifier("foobar".to_string()),
            SourcePos::new_at("stdio", "foobar", 5, 6, 1),
        ),
        Token::new(TokenContent::RBrace, SourcePos::new("stdio", "}")),
    ];
    let ts = TokenStream::from_slice(&tokens);
    let fields = BitSlice {
        start: 0,
        end: 16,
        name: "foobar".to_string(),
        pos: ts.slice(9..).get_pos(),
    };
    assert_eq!(
        field(ts),
        Ok((
            ts.slice(13..),
            Field {
                name: "foo".to_string(),
                base: "base".to_string(),
                offset: 0,
                length: 32,
                slices: vec![fields],
                pos: ts.get_pos()
            }
        ))
    );
}

#[test]
fn test_err() {
    let tokens = vec![
        Token::new(
            TokenContent::Identifier("foo".to_string()),
            SourcePos::new("stdio", "foo"),
        ),
        Token::new(TokenContent::LBracket, SourcePos::new("stdio", "[")),
        Token::new(
            TokenContent::Identifier("base".to_string()),
            SourcePos::new("stdio", "base"),
        ),
        Token::new(TokenContent::Comma, SourcePos::new("stdio", ",")),
        Token::new(TokenContent::IntLiteral(0), SourcePos::new("stdio", "0")),
        Token::new(TokenContent::Comma, SourcePos::new("stdio", ",")),
        Token::new(TokenContent::IntLiteral(32), SourcePos::new("stdio", "0")),
        Token::new(TokenContent::RBracket, SourcePos::new("stdio", "]")),
        Token::new(TokenContent::LBrace, SourcePos::new("stdio", "{")),
    ];

    let token2 = vec![
        Token::new(TokenContent::IntLiteral(0), SourcePos::new("stdio", "0")),
        Token::new(
            TokenContent::IntLiteral(16),
            SourcePos::new_at("stdio", "16", 2, 3, 1),
        ),
        Token::new(
            TokenContent::Identifier("foobar".to_string()),
            SourcePos::new_at("stdio", "foobar", 5, 6, 1),
        ),
    ];

    let token3 = vec![Token::new(
        TokenContent::RBrace,
        SourcePos::new("stdio", "}"),
    )];

    let mut t: Vec<Token> = Vec::new();
    t.extend(tokens);
    t.extend(token3);
    let ts = TokenStream::from_slice(&t);
    assert!(field(ts).is_err());
}
