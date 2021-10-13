// Velosiraptor Parser
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

///! Parameter Parsing
// nom library
use nom::{combinator::cut, sequence::preceded};

use crate::ast::Param;
use crate::error::IResult;
use crate::parser::terminals::{colon, ident, typeinfo};
use crate::token::TokenStream;

/// parses a single parameter
///
/// This function parses a single, typed parameter
///
/// # Grammar
///
/// ARG     := IDENT : TYPE
///
/// # Results
///
///  * OK:      the parser could successfully recognize the parameter
///  * Error:   the parser could not recognize the parameter
///  * Failure: the parser recognized the parameter, but it did not properly parse
///
/// # Examples
///
/// `a : bool`
///
pub fn parameter(input: TokenStream) -> IResult<TokenStream, Param> {
    // parse the identifier of the parameter
    let (i1, name) = ident(input.clone())?;

    // next, parse the type info
    let (i2, ptype) = cut(preceded(colon, typeinfo))(i1)?;

    // create the token stream covering the entire method def
    let pos = input.expand_until(&i2);

    // return the result
    Ok((i2, Param { name, ptype, pos }))
}
