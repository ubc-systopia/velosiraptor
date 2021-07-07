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
use crate::parser::ast::Expr;
use crate::parser::ast::Operation;
use crate::parser::terminals::{ident, minus, num, plus};

// the used nom componets
use nom::{branch::alt, error::ErrorKind, error_position, sequence::tuple, Err, IResult};

pub fn identexpr(input: TokenStream) -> IResult<TokenStream, Expr> {
    match ident(input.clone()) {
        Ok((r, i)) => Ok((
            r,
            Expr::Identifier {
                ident: i,
                pos: input.input_sourcepos(),
            },
        )),
        Err(x) => Err(x),
    }
}

pub fn numexpr(input: TokenStream) -> IResult<TokenStream, Expr> {
    match num(input.clone()) {
        Ok((r, i)) => Ok((
            r,
            Expr::Number {
                value: i,
                pos: input.input_sourcepos(),
            },
        )),
        Err(x) => Err(x),
    }
}

pub fn op(input: TokenStream) -> IResult<TokenStream, Operation> {
    match plus(input.clone()) {
        Ok((r, i)) => Ok((r, Operation::Plus)),
        Err(x) => Err(x),
    }
}

/// Parses a expression
///
///
pub fn expression(input: TokenStream) -> IResult<TokenStream, Expr> {
    // record the position
    let pos = input.input_sourcepos();

    // match ident or number
    let (i1, e1) = match alt((identexpr, numexpr))(input) {
        Ok((i, m)) => (i, m),
        Err(x) => return Err(x),
    };

    let (i2, op) = match op(i1.clone()) {
        Ok((i2, m)) => ((i2, m)),
        Err(x) => return Ok((i1, e1)),
    };

    let (i3, e2) = match expression(i2.clone()) {
        Ok((i3, m)) => ((i3, m)),
        Err(x) => return Err(x),
    };

    Ok((
        i3,
        Expr::BinOp {
            op,
            lhs: Box::new(e1),
            rhs: Box::new(e2),
            pos: i2.input_sourcepos(),
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
    let sp = SourcePos::new("stdio", " 1 + 2");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);

    assert!(expression(ts).is_ok());

    let sp = SourcePos::new("stdio", " 1 + 2 + 2 + 4 + 5");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(expression(ts).is_ok());

    let sp = SourcePos::new("stdio", " 1 + a + b + 4 + 5");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(expression(ts).is_ok());
}
