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
use crate::ast::ast::BitSlice;
use crate::lexer::token::TokenStream;
use crate::parser::terminals::{ident, num};

// the used nom componets
use nom::{error::ErrorKind, error_position, sequence::tuple, Err, IResult};

/// Parses a bitslice definition
///
/// a [BitSlice] represents a slice of bits within a field.
/// It lists the start, and end bits with an identifier.
///
/// # Requirements
///
/// The start bit shall be less or equal to the end bit number.
/// The end bit shall be within the supported range of the field
///
/// Note: those requirements are NOT checked in the parsing part.
///
/// # Example
///
/// `0 15 foobar` -- represents bits 0 to 15 and associate the identifier "foobar":
/// `0  0 bar`    -- represents bit 0 and associates the identifier "bar"
///
pub fn bitslice(input: TokenStream) -> IResult<TokenStream, BitSlice> {
    // record the current position of the bit slice
    let pos = input.input_sourcepos();

    // the first thing here shall be a number, just return the error here
    let (i1, start) = num(input.clone())?;
    let start = start as u16;

    // we match two numbers and an identifier
    let (rem, end, name) = match tuple((num, ident))(i1) {
        Ok((rem, (e, id))) => (rem, e as u16, id),
        Err(e) => {
            // if we have parser failure, indicate this!
            let (i, k) = match e {
                Err::Error(e) => (e.input, e.code),
                Err::Failure(e) => (e.input, e.code),
                Err::Incomplete(_) => (input, ErrorKind::Eof),
            };
            return Err(Err::Failure(error_position!(i, k)));
        }
    };

    Ok((
        rem,
        BitSlice {
            start,
            end,
            name,
            pos,
        },
    ))
}

#[cfg(test)]
use crate::lexer::{sourcepos::SourcePos, Lexer};

#[cfg(test)]
use crate::nom::Slice;

#[test]
fn test_ok() {
    // corresponds to `0 16 foobar`
    let sp = SourcePos::new("stdio", "0 16 foobar");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    let ts = TokenStream::from_vec(tokens);

    let pos = ts.input_sourcepos();
    let ts2 = ts.slice(3..);
    assert_eq!(
        bitslice(ts),
        Ok((
            ts2,
            BitSlice {
                start: 0,
                end: 16,
                name: "foobar".to_string(),
                pos
            }
        ))
    );
}

#[test]
fn test_err() {
    // corresponds to `0 foobar` missing end bit
    let sp = SourcePos::new("stdio", "0 foobar");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    let ts = TokenStream::from_vec(tokens);
    let ts2 = ts.slice(1..);
    assert_eq!(
        bitslice(ts),
        Err(Err::Failure(error_position!(ts2, ErrorKind::Digit)))
    );

    // corresponds to `0 16`  missing identifier
    let sp = SourcePos::new("stdio", "0 16 1");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    let ts = TokenStream::from_vec(tokens);
    let ts2 = ts.slice(2..);
    assert_eq!(
        bitslice(ts),
        Err(Err::Failure(error_position!(ts2, ErrorKind::AlphaNumeric)))
    );
}
