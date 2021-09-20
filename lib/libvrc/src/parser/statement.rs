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

//! Statement parsing

// the used nom componets
use nom::{
    branch::alt,
    combinator::cut,
    multi::many1,
    sequence::{delimited, pair, terminated},
};

// lexer, parser terminals and ast
use crate::ast::{Stmt, Type};
use crate::error::IResult;
use crate::parser::{
    expression::{arith_expr, bool_expr},
    terminals::{
        assign, colon, ident, kw_assert, kw_else, kw_if, kw_let, lbrace, lparen, rbrace, rparen,
        semicolon, typeinfo,
    },
};
use crate::token::TokenStream;

/// parses a let statement
///
/// The let statement defines a local variable with a given value
///
/// # Grammar
///
/// `STMT_LET := KW_LET IDENTIFIER : TYPE = EXPR;`
///
/// # Results
///
///  * OK:       when the parser successfully recognizes the let statemenet
///  * Error:    when the parse could not recognize the let statement
///  * Failure:  when the parser recognizes the let statement, but it is malformed
///
/// # Examples
///
/// `let x : int = 123;`
///
fn let_stmt(input: TokenStream) -> IResult<TokenStream, Stmt> {
    // get the input position
    let pos = input.input_sourcepos();

    // try to parse the `let` keyword, return error otherwise
    let (i1, _) = kw_let(input)?;

    // parse the LHS identifier and type information `IDENT : TYPE =`
    let (i2, (lhs, ti)) = cut(pair(ident, delimited(colon, typeinfo, assign)))(i1)?;

    // parse the RHS expression, currently we support boolean and arithmetic expressions
    let (i3, rhs) = match ti {
        Type::Boolean => cut(terminated(bool_expr, semicolon))(i2),
        _ => cut(terminated(arith_expr, semicolon))(i2),
    }?;

    // parsing successful, construct the token
    Ok((
        i3,
        Stmt::Assign {
            typeinfo: ti,
            lhs,
            rhs,
            pos,
        },
    ))
}

/// parses an assert statement
///
/// The assert statement provides additional information/checks to the system
///
/// # Grammar
///
/// `STMT_ASSERT := KW_ASSERT ( BOOL_EXPR );`
///
/// # Results
///
///  * OK:       when the parser successfully recognizes the assert statemenet
///  * Error:    when the parse could not recognize the assert statement
///  * Failure:  when the parser recognizes the assert statement, but it is malformed
///
/// # Examples
///
/// `assert(in > 4);
fn assert_stmt(input: TokenStream) -> IResult<TokenStream, Stmt> {
    // get the input position
    let pos = input.input_sourcepos();

    // try to parse the `let` keyword, return error otherwise
    let (i1, _) = kw_assert(input)?;

    let (i2, expr) = cut(terminated(delimited(lparen, bool_expr, rparen), semicolon))(i1)?;

    Ok((i2, Stmt::Assert { expr, pos }))
}

/// parser the if/else statement
fn if_else_stmt(input: TokenStream) -> IResult<TokenStream, Stmt> {
    let pos = input.input_sourcepos();
    // try to parse the `if` keyword, return error otherwise
    let (input, _tok) = kw_if(input)?;

    let (input, (cond, then)) = pair(bool_expr, delimited(lbrace, stmt, rbrace))(input)?;

    match kw_else(input.clone()) {
        Ok((input, _)) => match delimited(lbrace, stmt, rbrace)(input) {
            Ok((rem, stmt)) => Ok((
                rem,
                Stmt::IfElse {
                    cond,
                    then: Box::new(then),
                    other: Some(Box::new(stmt)),
                    pos,
                },
            )),
            Err(e) => Err(e),
        },
        Err(_) => Ok((
            input,
            Stmt::IfElse {
                cond,
                then: Box::new(then),
                other: None,
                pos,
            },
        )),
    }
}

/// Parses a statement
///
/// It tries to recognize a single statement
///
/// # Grammar
///  `STMT := STMT_LET | STMT_ASSERT |
///
/// # Results
///
///z
pub fn stmt(input: TokenStream) -> IResult<TokenStream, Stmt> {
    let pos = input.input_sourcepos();
    let (i, stmts) = many1(alt((if_else_stmt, let_stmt, assert_stmt)))(input)?;
    Ok((i, Stmt::Block { stmts, pos }))
}

#[test]
fn test_ok() {}
