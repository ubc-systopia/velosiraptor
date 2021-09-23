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
    combinator::{cut, opt},
    multi::many1,
    sequence::{delimited, pair, preceded, terminated, tuple},
};

// lexer, parser terminals and ast
use crate::ast::{Stmt, Type};
use crate::error::IResult;
use crate::parser::{
    expression::{arith_expr, bool_expr, expr},
    terminals::{
        assign, colon, ident, kw_assert, kw_else, kw_if, kw_let, kw_return, lbrace, lparen, rbrace,
        rparen, semicolon, typeinfo,
    },
};
use crate::token::TokenStream;

/// parses a return statement
///
/// The return statement produces the return value of a method
///
/// # Grammar
///
/// `STMT_RETURN := KW_RETURN EXPR;
///
/// # Example
///
/// `return 4;`
/// `return state.foo;`
///
fn return_stmt(input: TokenStream) -> IResult<TokenStream, Stmt> {
    // try to parse the `let` keyword, return error otherwise
    let (i1, _) = kw_return(input.clone())?;

    // parse the LHS identifier and type information `IDENT : TYPE =`
    let (i2, exp) = cut(terminated(expr, semicolon))(i1)?;

    // create the token stream covering the entire assert statement
    let pos = input.expand_until(&i2);

    // parsing successful, construct the token
    Ok((i2, Stmt::Return { expr: exp, pos }))
}

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
    // try to parse the `let` keyword, return error otherwise
    let (i1, _) = kw_let(input.clone())?;

    // parse the LHS identifier and type information `IDENT : TYPE =`
    let (i2, (lhs, ti)) = cut(pair(ident, delimited(colon, typeinfo, assign)))(i1)?;

    // parse the RHS expression, currently we support boolean and arithmetic expressions
    let (i3, rhs) = match ti {
        Type::Boolean => cut(terminated(bool_expr, semicolon))(i2),
        _ => cut(terminated(arith_expr, semicolon))(i2),
    }?;

    // create the token stream covering the entire let statement
    let pos = input.expand_until(&i3);

    // parsing successful, construct the token
    Ok((
        i3,
        Stmt::Let {
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
///
fn assert_stmt(input: TokenStream) -> IResult<TokenStream, Stmt> {
    // try to parse the `let` keyword, return error otherwise
    let (i1, _) = kw_assert(input.clone())?;

    let (i2, expr) = cut(terminated(delimited(lparen, bool_expr, rparen), semicolon))(i1)?;

    // create the token stream covering the entire assert statement
    let pos = input.expand_until(&i2);

    Ok((i2, Stmt::Assert { expr, pos }))
}

/// parses an if/else statement
///
/// The if/else statement provides a conditional branching.
/// The branches of the if/else statement must have at least one statement
///
/// # Grammar
///
/// STMT_IFELSE := KW_IF EXPR { STMT } [KW_ELSE { EXPR }]
///
/// # Results
///
///  * OK:       when the parser successfully recognizes the if/else statemenet
///  * Error:    when the parse could not recognize the if/else statement
///  * Failure:  when the parser recognizes the if/else statement, but it is malformed
///
/// # Examples
///
/// `if a < 0 { foo; } else { bar; }`
///
fn if_else_stmt(input: TokenStream) -> IResult<TokenStream, Stmt> {
    // try to parse the `if` keyword, return error otherwise
    let (i1, _tok) = kw_if(input.clone())?;

    // parses the block of statement

    let then_block = cut(delimited(lbrace, many1(stmt), rbrace));
    let else_block = preceded(kw_else, cut(delimited(lbrace, many1(stmt), rbrace)));

    let (i2, (cond, then, other)) = tuple((bool_expr, then_block, opt(else_block)))(i1)?;

    // create the token stream covering the entire method def
    let pos = input.expand_until(&i2);

    Ok((
        i2,
        Stmt::IfElse {
            cond,
            then,
            other: other.unwrap_or_default(),
            pos,
        },
    ))
}

/// parses a statement
///
/// This parser recognizes a single of the possible statements
///
/// # Grammar
///  `STMT := STMT_LET | STMT_ASSERT | STMT_IFELSE | STMT_RETURN
///
/// # Results
///
///  * OK:       when the parser successfully recognizes one of the statements
///  * Error:    when the parse could not recognize any of the statements
///  * Failure:  when any of the sub parsers results in the failure state
///
pub fn stmt(input: TokenStream) -> IResult<TokenStream, Stmt> {
    alt((if_else_stmt, let_stmt, assert_stmt, return_stmt))(input)
}

#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::sourcepos::SourcePos;

#[test]
fn test_ok() {
    let sp = SourcePos::new("stdio", "let x : int = 1234;");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(stmt(ts).is_ok());

    let sp = SourcePos::new("stdio", "assert(x < 5);");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(stmt(ts).is_ok());

    let sp = SourcePos::new("stdio", "return 5;");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(stmt(ts).is_ok());

    let sp = SourcePos::new("stdio", "if 5 < 4 { return 5; }");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(stmt(ts).is_ok());

    let sp = SourcePos::new("stdio", "if 5 < 4 { return 5; } else {return 4;}");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(stmt(ts).is_ok());
}
#[test]
fn test_fail() {
    let sp = SourcePos::new("stdio", "assert(x + 5);");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(stmt(ts).is_err());

    let sp = SourcePos::new("stdio", "if 5 + 4 { return 5; }");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(stmt(ts).is_err());
}
