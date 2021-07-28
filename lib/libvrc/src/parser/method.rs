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

//! Implementation of method parsing

use crate::ast::{Method, Stmt, Type};
use crate::error::IResult;
use crate::parser::statement::stmt;
use crate::parser::terminals::{
    colon, comma, ident, kw_fn, lbrace, lparen, rarrow, rbrace, rparen, semicolon, typeinfo,
};
use crate::token::TokenStream;
use nom::combinator::cut;
use nom::multi::separated_list0;
use nom::sequence::{delimited, pair, preceded, terminated};

// TODO add tests

/// Parses and consumes a method from a unit body
///
/// example of method syntax:
/// fn method_name(arg1: Size, arg2: Integer, arg3: Boolean) -> Address {
///     stmt;
///     stmt;
///     return stmt;
/// }
pub fn method(input: TokenStream) -> IResult<TokenStream, Method> {
    // parse and consume fn keyword
    let (i1, _) = kw_fn(input.clone())?;

    // parse and consume method name
    let (i2, name) = cut(ident)(i1)?;

    // parse and consume a list of arguments
    let (i3, args) = cut(typed_arguments)(i2)?;

    // parse and consume a return type
    let (i4, rettype) = cut(preceded(rarrow, typeinfo))(i3)?;

    // parse and consume a function body (or an abstract function)
    let (i5, stmts) = cut(method_body)(i4)?;

    let is_abstract = false;
    // create the token stream covering the entire method def
    let pos = input.expand_until(&i5);

    Ok((
        i5,
        Method {
            name,
            rettype,
            args,
            stmts,
            pos,
            is_abstract,
        },
    ))
}

fn method_body(input: TokenStream) -> IResult<TokenStream, Vec<Stmt>> {
    delimited(
        lbrace,
        terminated(separated_list0(semicolon, stmt), semicolon),
        rbrace,
    )(input)
}

fn typed_arguments(input: TokenStream) -> IResult<TokenStream, Vec<(String, Type)>> {
    delimited(
        lparen,
        separated_list0(comma, pair(ident, preceded(colon, typeinfo))),
        rparen,
    )(input)
}
