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

//! State definition parsing

// lexer, parser terminals and ast
use crate::lexer::token::TokenStream;
use crate::parser::ast::BitSlice;
use crate::parser::terminals::{ident, num};

// the used nom componets
use nom::error::ErrorKind;
use nom::sequence::tuple;
use nom::{error_position, Err, IResult};

/// Parses a bitslice definition
///
///
pub fn bitslice(input: TokenStream) -> IResult<TokenStream, BitSlice> {
    // the first thing here shall be a number
    let (i1, start) = match num(input) {
        Ok((rem, s)) => (rem, s),
        Err(x) => return Err(x),
    };

    // we match two numbers and an identifier
    let (rem, end, name) = match tuple((num, ident))(i1) {
        Ok((rem, (e, id))) => (rem, e, id),
        Err(e) => {
            // if we have parser failure, indicate this!
            let (i, k) = match e {
                Err::Error(e) => (e.input, e.code),
                _ => (i1, ErrorKind::AlphaNumeric),
            };
            return Err(Err::Failure(error_position!(i, k)));
        }
    };

    Ok((
        rem,
        BitSlice::new(start as u16, end as u16, name, input.get_pos()),
    ))
}

#[cfg(test)]
use crate::lexer::sourcepos::SourcePos;
#[cfg(test)]
use crate::lexer::token::{Token, TokenContent};
#[cfg(test)]
use crate::nom::Slice;

#[test]
fn test_ok() {
    // corresponds to `0 16 foobar`
    let tokens = vec![
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
    let ts = TokenStream::from_slice(&tokens);

    assert_eq!(
        bitslice(ts),
        Ok((
            ts.slice(3..),
            BitSlice {
                start: 0,
                end: 16,
                name: "foobar".to_string(),
                pos: ts.get_pos()
            }
        ))
    );
}
#[test]
fn test_err() {
    // corresponds to `0 foobar` missing end bit
    let tokens = vec![
        Token::new(TokenContent::IntLiteral(0), SourcePos::new("stdio", "0")),
        Token::new(
            TokenContent::Identifier("foobar".to_string()),
            SourcePos::new_at("stdio", "foobar", 5, 6, 1),
        ),
    ];
    let ts = TokenStream::from_slice(&tokens);

    assert_eq!(
        bitslice(ts),
        Err(Err::Failure(error_position!(
            ts.slice(1..),
            ErrorKind::Digit
        )))
    );

    // corresponds to `0 16`  missing identifier
    let tokens = vec![
        Token::new(TokenContent::IntLiteral(0), SourcePos::new("stdio", "0")),
        Token::new(
            TokenContent::IntLiteral(16),
            SourcePos::new_at("stdio", "16", 2, 3, 1),
        ),
    ];
    let ts = TokenStream::from_slice(&tokens);

    assert_eq!(
        bitslice(ts),
        Err(Err::Failure(error_position!(
            ts.slice(1..),
            ErrorKind::AlphaNumeric
        )))
    );
}
