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

// the used nom functions
use nom::{
    combinator::{cut, opt},
    multi::{many0, separated_list0},
    sequence::{delimited, preceded, terminated, tuple},
};

// library internal includes
use crate::ast::{Expr, Method, Stmt, Type};
use crate::error::IResult;
use crate::parser::{
    expression::bool_expr,
    statement::stmt,
    terminals::{
        colon, comma, ident, kw_ensures, kw_fn, kw_requires, lbrace, lparen, rarrow, rbrace,
        rparen, semicolon, typeinfo,
    },
};
use crate::token::TokenStream;

/// Parses a require clause
///
/// This adds a pre-condition to the function/method
///
/// # Results
///
///  * OK:      the parser could successfully recognize the requires clause
///  * Error:   the parser could not recognize the requires clause
///  * Failure: the parser recognized the requires clause, but it did not properly parse
///
/// # Examples
///
/// `requires arg > 0`
pub fn require_clauses(input: TokenStream) -> IResult<TokenStream, Expr> {
    let (i1, _) = kw_requires(input)?;
    cut(terminated(bool_expr, semicolon))(i1)
}

/// Parses a ensures clause
///
/// This adds a post-condition to the function/method.
///
/// # Results
///
///  * OK:      the parser could successfully recognize the ensures clause
///  * Error:   the parser could not recognize the ensures clause
///  * Failure: the parser recognized the ensures clause, but it did not properly parse
///
/// # Examples
///
/// `ensures ret < 5`
pub fn ensure_clauses(input: TokenStream) -> IResult<TokenStream, Expr> {
    let (i1, _) = kw_ensures(input)?;
    cut(terminated(bool_expr, semicolon))(i1)
}

/// Parses and consumes a method from a unit body
///
/// # Examples
///
/// example of method syntax:
/// fn method_name(arg1: Size, arg2: Integer, arg3: Boolean) -> Address {
///     stmt;
///     stmt;
///     return stmt;
/// }
///
/// Another example with pre-/post conditions
/// fn method_name(arg1: Size, arg2: Integer, arg3: Boolean) -> Address
///    requires arg1 > 4
///    ensures  ret < 3
/// {
///     stmt;
///     stmt;
///     return stmt;
/// }
pub fn method(input: TokenStream) -> IResult<TokenStream, Method> {
    // parse and consume fn keyword
    let (i1, _) = kw_fn(input.clone())?;

    // get the method name and the arguments
    let (i2, (name, args)) = cut(tuple((ident, typed_arguments)))(i1)?;

    // get the return type
    let (i3, rettype) = cut(preceded(rarrow, typeinfo))(i2)?;

    // get the ensure clauses
    let (i4, (requires, ensures)) = tuple((many0(require_clauses), many0(ensure_clauses)))(i3)?;

    // parse and consume a function body (or an abstract function)
    let (i5, stmts) = cut(opt(method_body))(i4)?;

    let is_abstract = false;
    // create the token stream covering the entire method def
    let pos = input.expand_until(&i5);

    Ok((
        i5,
        Method {
            name,
            rettype,
            args,
            requires,
            ensures,
            stmts: stmts.unwrap_or(Vec::new()),
            pos,
            is_abstract,
        },
    ))
}

fn method_body(input: TokenStream) -> IResult<TokenStream, Vec<Stmt>> {
    delimited(lbrace, many0(stmt), rbrace)(input)
}

fn typed_arguments(input: TokenStream) -> IResult<TokenStream, Vec<(String, Type)>> {
    delimited(
        lparen,
        separated_list0(comma, tuple((ident, preceded(colon, typeinfo)))),
        rparen,
    )(input)
}

#[cfg(test)]
use crate::lexer::Lexer;

#[test]
fn test_ok() {
    let tokens = Lexer::lex_string("stdio", "fn foo() -> addr { let x : int = 3; }").unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(method(ts).is_ok());

    let tokens = Lexer::lex_string(
        "stdio",
        "fn foo() -> addr requires x > 0; ensures y < 3; { let x : int = 3; }",
    )
    .unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(method(ts).is_ok());

    // an abstract function
    let tokens = Lexer::lex_string("stdio", "fn foo() -> addr;").unwrap();
    let ts = TokenStream::from_vec(tokens);
    println!("{:?}", method(ts.clone()));
    assert!(method(ts).is_ok());
}
