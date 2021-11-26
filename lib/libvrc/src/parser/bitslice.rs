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
use crate::ast::BitSlice;
use crate::error::IResult;
use crate::parser::terminals::{ident, lbrace, num, rbrace, semicolon};
use crate::token::TokenStream;

// the used nom components
use nom::{
    combinator::cut,
    multi::many1,
    sequence::{delimited, terminated, tuple},
};

/// Parses a bitslice definition
///
/// a [BitSlice] represents a slice of bits within a field.
/// It lists the start, and end bits with an identifier.
///
/// # Grammar
///
/// BITSLICE := NUM NUM IDENT ";"
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
    // the first thing here shall be a number, just return the error here
    let (i1, start) = num(input.clone())?;

    // we match two numbers and an identifier
    let (rem, (end, name)) = cut(terminated(tuple((num, ident)), semicolon))(i1)?;

    // swap start and end if they are the other way round.
    let (start, end) = if end < start {
        (end, start)
    } else {
        (start, end)
    };

    // calculate the position of the bitslice
    let pos = input.expand_until(&rem);

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

/// parses a block of bit slices
///
/// This parse recognizes a block of bitslices.
///
/// # Grammar
///
/// BITSLICE_BLOCK := "{" BITSLICE+  "}"
///
/// # Results
///
///  * OK:      the parser could successfully recognize the bitslice blcok
///  * Error:   the parser could not recognize the bitslice block
///  * Failure: the parser recognized the interface field, but it did not properly parse
///
/// # Examples
///
///  - just the width: [8]
///  - base offset, width: [base, 4, 4]
///
pub fn bitslice_block(input: TokenStream) -> IResult<TokenStream, Vec<BitSlice>> {
    delimited(lbrace, cut(many1(bitslice)), cut(rbrace))(input)
}

#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::nom::Slice;
#[cfg(test)]
use crate::sourcepos::SourcePos;

#[test]
fn test_ok() {
    // corresponds to `0 16 foobar`
    let sp = SourcePos::new("stdio", "0 16 foobar;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    let ts = TokenStream::from_vec(tokens);

    let pos = ts.slice(0..4);
    let ts2 = ts.slice(4..);
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
    let sp = SourcePos::new("stdio", "0 foobar;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(bitslice(ts).is_err());

    let sp = SourcePos::new("stdio", "0 1 foobar");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(bitslice(ts).is_err());

    // corresponds to `0 16`  missing identifier
    let sp = SourcePos::new("stdio", "0 16 1;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(bitslice(ts).is_err())
}
