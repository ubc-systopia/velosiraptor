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

//! Constants Definition Parsing

// nom parser combinators
use nom::{
    sequence::{pair, terminated},
    IResult, Slice,
};

// nom error handling
use nom::{error::ErrorKind, error_position, Err};

// lexer / parser imports
use crate::ast::ast::Const;
use crate::lexer::token::TokenStream;
use crate::parser::terminals::{assign, ident, kw_const, num, semicolon};

/// parses a constat item of a unit
///
/// `const IDENT = 123;`
pub fn constdef(input: TokenStream) -> IResult<TokenStream, Const> {
    // obtain the current source position
    let pos = input.input_sourcepos();

    // parse the `const` keyword, return otherwise
    let (i1, _) = kw_const(input)?;

    match pair(terminated(ident, assign), terminated(num, semicolon))(i1.clone()) {
        Ok((rem, (ident, value))) => Ok((
            rem,
            Const::Integer {
                ident,
                value,
                pos: pos.slice(0..5),
            },
        )),
        Err(x) => {
            // if we have parser failure, indicate this!
            let (i, k) = match x {
                Err::Error(e) => (e.input, e.code),
                Err::Failure(e) => (e.input, e.code),
                Err::Incomplete(_) => (i1, ErrorKind::Eof),
            };
            Err(Err::Failure(error_position!(i, k)))
        }
    }
}

#[cfg(test)]
use crate::lexer::{sourcepos::SourcePos, Lexer};

#[test]
fn test_ok() {
    // corresponds to `0 16 foobar`
    let sp = SourcePos::new("stdio", "const FOO = 1234;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    let ts = TokenStream::from_vec(tokens);

    assert_eq!(
        constdef(ts.clone()),
        Ok((
            ts.slice(5..6),
            Const::new("FOO".to_string(), 1234, sp.slice(0..5))
        ))
    );
}

#[test]
fn test_fails() {
    // corresponds to `0 16 foobar`
    let sp = SourcePos::new("stdio", "const FOO = 1234 asdf");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    let ts = TokenStream::from_vec(tokens);

    assert!(constdef(ts).is_err());

    let sp = SourcePos::new("stdio", "const FOO = asdf;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    let ts = TokenStream::from_vec(tokens);

    assert!(constdef(ts).is_err());

    let sp = SourcePos::new("stdio", "FOO = asdf;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    let ts = TokenStream::from_vec(tokens);

    assert!(constdef(ts).is_err());
}
