// VelosiParser -- Parser for the VelosiRaptor specification language
//
//
// MIT License
//
// Copyright (c) 2021-2023 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiParser: Types
//!
//! This module contains the a parser for (extern) type declarations used in the
//! OS specifications

// external dependencies
use nom::{
    combinator::{cut, opt},
    multi::separated_list0,
    sequence::{delimited, tuple},
};

// used crate functionality
use crate::error::IResult;

use crate::parser::parameter::param;
use crate::parser::terminals::{comma, ident, kw_extern, kw_type, lbrace, rbrace};
use crate::parsetree::VelosiParseTreeExternType;
use crate::VelosiTokenStream;

/// parses and consumes an external type declaration
///
/// The external type declaration provides information about a type that is defined by the
/// operating system environment.
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized type definition as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `IMPORT := KW_EXTERN KW_TYPE IDENT LBRACE ... RBRACE`
///
/// # Examples
///
///  * `extern type Frame { field: type, field: type };`
///
pub fn extern_type(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeExternType> {
    let mut loc = input.clone();

    let (i1, _) = tuple((kw_extern, kw_type))(input)?;

    let (i2, ident) = cut(ident)(i1)?;
    let (i3, fields) = cut(delimited(
        lbrace,
        separated_list0(comma, param),
        tuple((opt(comma), rbrace)),
    ))(i2)?;

    loc.span_until_start(&i3);

    let ty = VelosiParseTreeExternType { ident, fields, loc };

    Ok((i3, ty))
}
