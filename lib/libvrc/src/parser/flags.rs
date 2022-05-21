// Velosiraptor Compiler
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! Flags Definition Parsing

// nom parser combinators
use nom::{
    combinator::cut,
    multi::many1,
    sequence::{delimited, pair, preceded},
};

// lexer / parser imports
use crate::ast::{Flag, Flags};
use crate::error::IResult;
use crate::parser::terminals::{assign, ident, kw_flags, lbrace, num, rbrace, semicolon};
use crate::token::TokenStream;

/// parses the flag defintion
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [Flag] and the remaining [TokenStream] if the parser succeeded,
/// or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// `FLAG := IDENT = NUM SEMICOLON`
///
/// # Example
///
///  * `WRITE = 1`
///
/// # Notes
///
///  * None
///
pub fn flag(input: TokenStream) -> IResult<TokenStream, Flag> {
    let (i, (name, value)) = pair(ident, cut(delimited(assign, num, semicolon)))(input.clone())?;

    let f = Flag::new(name, input).set_value(value).finalize(&i);

    Ok((i, f))
}

/// parses the flags construct of a unit
///
/// # Arguments
///
///  * `input`  - token stream representing the current input position
///
/// # Return Value
///
/// Result type wrapping a [Vec<Flag>] and the remaining [TokenStream] if the parser succeeded,
/// or an error wrapping the input position if the parser failed.
///
/// # Grammar
///
/// `FLAGS := KW_FLAGS ASSIGN LBRACE (FLAG)+ RBRACE`
///
/// # Example
///
///  * `flags = { WRITE = 1 }`
///
/// # Notes
///
///  * None
///
pub fn flags(input: TokenStream) -> IResult<TokenStream, Flags> {
    // parse the `const` keyword, return otherwise
    let (i1, _) = kw_flags(input.clone())?;

    // parse the flags body
    let (i2, flags) = cut(preceded(assign, delimited(lbrace, many1(flag), rbrace)))(i1)?;

    let f = Flags::new(input).add_flags(flags).finalize(&i2);

    Ok((i2, f))
}
