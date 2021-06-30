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

// the result type
use nom::IResult;

// get the tokens
use crate::parser::terminals::{ident, colon, unit_keyword, lbrace, rbrace};

use crate::lexer::token::TokenStream;

use nom::error::ErrorKind;
use nom::{error_position, Err};
use nom::sequence::{preceded, delimited};
use nom::combinator::opt;

use crate::parser::ast::Unit;

/// parses and consumes an import statement (`unit foo {};`) and any following whitespaces
pub fn unit(input: TokenStream) -> IResult<TokenStream, Unit> {
    // try to parse the

    // try to match the input keyword, there is no match, return.
    let i1 = match unit_keyword(input) {
        Ok((input, _)) => input,
        Err(x) => return Err(x),
    };

    // ok, so we've seen the `unit` keyword, so the next must be an identifier.
    let (i1, unitname) = match ident(i1) {
        Ok((i, u)) => (i, u),
        Err(_) => return Err(Err::Failure(error_position!(
            input,
            ErrorKind::AlphaNumeric
        ))),
    };

    // is it a derived type, then we may see a ` : type` clause
    let (i2, supertype) = match opt(preceded(colon, ident))(i1) {
        Ok((i, s)) => (i, s),
        // possibly check here for an error!
        Err(_)   => (i1, None)
    };

    // TODO: firmulate the body
    let unitbody = colon;

    // then we have the unit block, wrapped in curly braces
    let (i3, _) = match delimited(lbrace, unitbody, rbrace)(i2) {
        Ok((i, b)) => (i, b),
        Err(_)     => return Err(Err::Failure(error_position!(
            input,
            ErrorKind::AlphaNumeric
        ))),
    };

    Ok((i3, Unit::new(unitname, supertype, input.get_pos())))
}
