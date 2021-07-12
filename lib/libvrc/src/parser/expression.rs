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
use crate::lexer::sourcepos::SourcePos;
use crate::lexer::token::TokenStream;
use crate::parser::ast::Expr;
use crate::parser::ast::{BinOp, UnOp};
use crate::parser::terminals::*;

// Precedence of Operators  (strong to weak)
// Operator                         Associativity       Example
// Paths                                                a::b
// Method calls                                         a.b()
// Field expressions                left to right       a.b.c
// Function calls, array indexing                       a()  a[1]
// ?                                                    ?
// Unary - * ! & &mut                                   !a
// as                               left to right       as
// * / %                            left to right       a * b, a / b, a % b
// + -                              left to right
// << >>                            left to right
// &                                left to right
// ^                                left to right
// |                                left to right
// == != < > <= >=                  Require parentheses
// &&                               left to right
// ||                               left to right
// .. ..=                           Require parentheses
// =                                                    Assign

// the used nom componets
use nom::{
    branch::alt,
    error::ErrorKind,
    error_position,
    sequence::{delimited, tuple},
    Err, IResult,
};

use nom::multi::many0;
use nom::sequence::{pair, preceded, terminated};

/// parses expressions
pub fn expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    lor_expr(input)
}

/// parses boolean expressions
pub fn bool_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    lor_expr(input)
}

/// parser arithmetic expressions
pub fn arith_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    lor_expr(input)
}

/// folds expressions
fn fold_exprs(initial: Expr, remainder: Vec<(SourcePos, BinOp, Expr)>) -> Expr {
    remainder.into_iter().fold(initial, |acc, tuple| {
        let (pos, op, expr) = tuple;
        Expr::BinaryOperation {
            op,
            lhs: Box::new(acc),
            rhs: Box::new(expr),
            pos,
        }
    })
}

pub fn lor_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = land_expr(input)?;

    let (i, remainder) = many0(|i: TokenStream| {
        let pos = i.input_sourcepos();
        let (i, add) = preceded(lor, land_expr)(i)?;
        Ok((i, (pos, BinOp::Lor, add)))
    })(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

pub fn land_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = cmp_expr(input)?;

    let (i, remainder) = many0(|i: TokenStream| {
        let pos = i.input_sourcepos();
        let (i, add) = preceded(land, cmp_expr)(i)?;
        Ok((i, (pos, BinOp::Land, add)))
    })(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

pub fn cmp_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = or_expr(input)?;
    let (i, remainder) = many0(alt((
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(eq, or_expr)(i)?;
            Ok((i, (pos, BinOp::Eq, op)))
        },
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(ne, or_expr)(i)?;
            Ok((i, (pos, BinOp::Ne, op)))
        },
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(gt, or_expr)(i)?;
            Ok((i, (pos, BinOp::Gt, op)))
        },
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(lt, or_expr)(i)?;
            Ok((i, (pos, BinOp::Lt, op)))
        },
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(le, or_expr)(i)?;
            Ok((i, (pos, BinOp::Le, op)))
        },
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(ge, or_expr)(i)?;
            Ok((i, (pos, BinOp::Ge, op)))
        },
    )))(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

pub fn or_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = xor_expr(input)?;

    let (i, remainder) = many0(|i: TokenStream| {
        let pos = i.input_sourcepos();
        let (i, op) = preceded(or, xor_expr)(i)?;
        Ok((i, (pos, BinOp::Or, op)))
    })(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

pub fn xor_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = and_expr(input)?;

    let (i, remainder) = many0(|i: TokenStream| {
        let pos = i.input_sourcepos();
        let (i, op) = preceded(xor, and_expr)(i)?;
        Ok((i, (pos, BinOp::Or, op)))
    })(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

pub fn and_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = shift_expr(input)?;

    let (i, remainder) = many0(|i: TokenStream| {
        let pos = i.input_sourcepos();
        let (i, op) = preceded(and, shift_expr)(i)?;
        Ok((i, (pos, BinOp::And, op)))
    })(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

pub fn shift_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = add_expr(input)?;
    let (i, remainder) = many0(alt((
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(lshift, add_expr)(i)?;
            Ok((i, (pos, BinOp::LShift, op)))
        },
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(rshift, add_expr)(i)?;
            Ok((i, (pos, BinOp::RShift, op)))
        },
    )))(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

/// parses a + / -
pub fn add_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = mul_expr(input)?;
    let (i, remainder) = many0(alt((
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(plus, mul_expr)(i)?;
            Ok((i, (pos, BinOp::Plus, op)))
        },
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(minus, mul_expr)(i)?;
            Ok((i, (pos, BinOp::Plus, op)))
        },
    )))(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

/// parses a * / %
pub fn mul_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = unary_expr(input)?;
    let (i, remainder) = many0(alt((
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(star, unary_expr)(i)?;
            Ok((i, (pos, BinOp::Multiply, op)))
        },
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(slash, unary_expr)(i)?;
            Ok((i, (pos, BinOp::Divide, op)))
        },
        |i: TokenStream| {
            let pos = i.input_sourcepos();
            let (i, op) = preceded(percent, unary_expr)(i)?;
            Ok((i, (pos, BinOp::Modulo, op)))
        },
    )))(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

fn unary_not(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let pos = input.input_sourcepos();
    let (i, val) = preceded(not, funcall_expr)(input)?;
    Ok((
        i,
        Expr::UnaryOperation {
            op: UnOp::LNot,
            val: Box::new(val),
            pos,
        },
    ))
}

fn unary_lnot(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let pos = input.input_sourcepos();
    let (i, val) = preceded(lnot, funcall_expr)(input)?;
    Ok((
        i,
        Expr::UnaryOperation {
            op: UnOp::LNot,
            val: Box::new(val),
            pos,
        },
    ))
}

pub fn unary_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    alt((unary_not, unary_lnot, funcall_expr))(input)
}

pub fn fn_call_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    let (i, e) = terminated(ident_expr, pair(lparen, rparen))(input)?;
    match e {
        Expr::Identifier { path, pos } => Ok((i, Expr::FnCall { path, pos })),
        _ => panic!("unexpected type"),
    }
}

pub fn slice_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    let (i, (p, e)) = pair(ident_expr, delimited(lbrack, expr, rbrack))(input)?;
    match p {
        Expr::Identifier { path, pos } => Ok((
            i,
            Expr::Slice {
                path,
                slice: Box::new(e),
                pos,
            },
        )),
        _ => panic!("unexpected type"),
    }
}

pub fn funcall_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    alt((slice_expr, fn_call_expr, value_expr))(input)
}

//
pub fn value_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    alt((paren_expr, literal_expr))(input)
}

pub fn num_lit_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let pos = input.input_sourcepos();
    let (rem, value) = num(input)?;
    Ok((rem, Expr::Number { value, pos }))
}

pub fn bool_lit_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let pos = input.input_sourcepos();
    let (rem, value) = boolean(input)?;
    Ok((rem, Expr::Boolean { value, pos }))
}

pub fn ident_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let pos = input.input_sourcepos();
    let (i, (fst, mut ot)) = pair(ident, many0(preceded(dot, ident)))(input)?;
    let mut path = Vec::from([fst]);
    path.append(&mut ot);
    Ok((i, Expr::Identifier { path, pos }))
}

pub fn literal_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    alt((num_lit_expr, bool_lit_expr, ident_expr))(input)
}

pub fn paren_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    delimited(lparen, expr, rparen)(input)
}

#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::nom::Slice;

#[test]
fn test_ok() {
    // corresponds to `0 16 foobar`
    let sp = SourcePos::new("stdio", "1");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(expr(ts).is_ok());

    let sp = SourcePos::new("stdio", "true");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(expr(ts).is_ok());

    let sp = SourcePos::new("stdio", "ident");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(expr(ts).is_ok());

    let sp = SourcePos::new("stdio", " 1 + 2 * 3 + 4 ");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert_eq!(
        expr(ts.clone()).map(|(i, x)| (i, format!("{}", x))),
        Ok((ts.slice(7..8), String::from("((1 + (2 * 3)) + 4)")))
    );

    let sp = SourcePos::new("stdio", " 1 + 2 * 3 + 4 << 5 * 2");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let len = tokens.len();
    let ts = TokenStream::from_vec(tokens);
    assert_eq!(
        expr(ts.clone()).map(|(i, x)| (i, format!("{}", x))),
        Ok((
            ts.slice(len - 1..len),
            String::from("(((1 + (2 * 3)) + 4) << (5 * 2))")
        ))
    );

    let sp = SourcePos::new("stdio", "a && b || c && d || x > 9");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let len = tokens.len();
    let ts = TokenStream::from_vec(tokens);
    assert_eq!(
        expr(ts.clone()).map(|(i, x)| (i, format!("{}", x))),
        Ok((
            ts.slice(len - 1..len),
            String::from("(((a && b) || (c && d)) || (x > 9))")
        ))
    );

    let sp = SourcePos::new("stdio", "a.a && b.b || c.x && d.d.a || x > 9 && !zyw");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let len = tokens.len();
    let ts = TokenStream::from_vec(tokens);
    assert_eq!(
        expr(ts.clone()).map(|(i, x)| (i, format!("{}", x))),
        Ok((
            ts.slice(len - 1..len),
            String::from("(((a.a && b.b) || (c.x && d.d.a)) || ((x > 9) && !(zyw)))")
        ))
    );

    let sp = SourcePos::new("stdio", " 1 + 2 + 2 + 4 + 5");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(expr(ts).is_ok());

    let sp = SourcePos::new("stdio", " 1 + a + b + 4 + 5");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(expr(ts).is_ok());
}
#[test]
fn test_err() {
    let sp = SourcePos::new("stdio", "a + b) && (c < 3) + 3");
    let tokens = Lexer::lex_source_pos(sp).unwrap();
    let ts = TokenStream::from_vec(tokens);
    let res = expr(ts.clone());
    let (r1, r2) = res.unwrap();
    println!("{}\n\n{}", r1, r2);
    assert!(expr(ts.clone()).is_err());
}
