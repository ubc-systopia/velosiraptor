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

// lexer, parser terminals and ast
use crate::ast::Expr;
use crate::ast::{Stmt, Type};
use crate::parser::expression::{arith_expr, bool_expr};
use crate::parser::terminals::{
    assign, colon, ident, kw_else, kw_if, kw_let, lbrace, rbrace, semicolon, typeinfo,
};
use crate::token::TokenStream;

// the used nom componets
use nom::{branch::alt, error_position, Err, IResult};
use nom::{
    combinator::cut,
    multi::many1,
    sequence::{delimited, pair, terminated},
};

/// parses a let statement
///
/// The let statement defines a local variable with a given value
/// For example: `let x = 123;`
///
/// The statement has the form:
/// `let IDENTIFIER = EXPR;`
fn let_stmt(input: TokenStream) -> IResult<TokenStream, Stmt> {
    let pos = input.input_sourcepos();

    // try to parse the `let` keyword, return error otherwise
    let (i1, _) = kw_let(input)?;

    // parse tye type information `IDENT : TYPE =`
    let (i2, (lhs, ti)) = cut(pair(ident, delimited(colon, typeinfo, assign)))(i1)?;

    // parse the expression
    let (i3, rhs) = match ti {
        Type::Boolean => cut(terminated(bool_expr, semicolon))(i2),
        _ => cut(terminated(arith_expr, semicolon))(i2),
    }?;

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

/// parser the if/else statement
fn if_else_stmt(input: TokenStream) -> IResult<TokenStream, Stmt> {
    let pos = input.input_sourcepos();
    // try to parse the `if` keyword, return error otherwise
    let (input, _tok) = kw_if(input)?;

    let (input, cond, then) = match pair(bool_expr, delimited(lbrace, stmt, rbrace))(input) {
        Ok((input, (cond, then))) => (input, cond, then),
        Err(e) => {
            // here we are having a parsing error!
            let (i, k) = match e {
                Err::Error(e) => (e.input, e.code),
                x => panic!("unkown condition: {:?}", x),
            };
            return Err(Err::Failure(error_position!(i, k)));
        }
    };

    match kw_else(input.clone()) {
        Ok((input, _)) => {
            match delimited(lbrace, stmt, rbrace)(input) {
                Ok((rem, stmt)) => Ok((
                    rem,
                    Stmt::IfElse {
                        cond,
                        then: Box::new(then),
                        other: Some(Box::new(stmt)),
                        pos,
                    },
                )),
                Err(e) => {
                    // here we are having a parsing error!
                    let (i, k) = match e {
                        Err::Error(e) => (e.input, e.code),
                        x => panic!("unkown condition: {:?}", x),
                    };
                    Err(Err::Failure(error_position!(i, k)))
                }
            }
        }
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

/// Parses a expression
///
///
pub fn stmt(input: TokenStream) -> IResult<TokenStream, Stmt> {
    let pos = input.input_sourcepos();
    let (i, stmts) = many1(alt((if_else_stmt, let_stmt)))(input)?;
    Ok((i, Stmt::Block { stmts, pos }))
}

#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::nom::Slice;
#[cfg(test)]
use crate::sourcepos::SourcePos;

#[test]
fn test_ok() {}
