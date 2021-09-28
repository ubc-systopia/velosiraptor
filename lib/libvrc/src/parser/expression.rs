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
use crate::ast::{AstNode, BinOp, Expr, UnOp};
use crate::error::IResult;
use crate::parser::terminals::*;
use crate::token::TokenStream;

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
// + -                              left to right       a + b, a - b
// << >>                            left to right       a << b, a >> b,
// &                                left to right       a & b
// ^                                left to right       a * b
// |                                left to right       a | b
// == != < > <= >=                  Require parentheses
// &&                               left to right
// ||                               left to right
// .. ..=                           Require parentheses
// =                                                    Assign

// the used nom componets
use nom::{
    branch::alt,
    combinator::cut,
    multi::many0,
    sequence::{delimited, tuple},
    sequence::{pair, preceded, terminated},
};

/// folds expressions
fn fold_exprs(initial: Expr, remainder: Vec<(BinOp, Expr)>) -> Expr {
    remainder.into_iter().fold(initial, |acc, tuple| {
        let (op, expr) = tuple;

        let pos = acc.loc().clone().merge(expr.loc());
        Expr::BinaryOperation {
            op,
            lhs: Box::new(acc),
            rhs: Box::new(expr),
            pos,
        }
    })
}

/// expression parsing: parses wither a boolean or arithmetic expression
pub fn expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    alt((bool_expr, range_expr, arith_expr))(input)
}

/// parses boolean expressions
///
/// this is an expression that evaluates to a boolean value.
pub fn bool_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    // we start with a the logical or (||) as this has the weakest precedence
    assert!(!input.is_empty());
    let (i, initial) = bool_land(input)?;

    let (i, remainder) = many0(|i: TokenStream| {
        let (i, add) = preceded(lor, bool_land)(i)?;
        Ok((i, (BinOp::Lor, add)))
    })(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

/// parses a range expression (a..b)
///
/// an arithmetic expression evalutes to a number a | b
pub fn range_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    let (i, (s, _, e)) = tuple((arith_expr, dotdot, arith_expr))(input.clone())?;
    let pos = input.merge(&i);
    Ok((
        i,
        Expr::Range {
            start: Box::new(s),
            end: Box::new(e),
            pos,
        },
    ))
}

/// parse arithmetic expressions
///
/// an arithmetic expression evalutes to a number a | b
pub fn arith_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    // we start with the or expression (|)
    assert!(!input.is_empty());
    let (i, initial) = arith_xor_expr(input)?;

    let (i, remainder) = many0(|i: TokenStream| {
        let (i, op) = preceded(or, arith_xor_expr)(i)?;
        Ok((i, (BinOp::Or, op)))
    })(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

pub fn num_lit_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, value) = num(input.clone())?;
    let pos = input.expand_until(&i);
    Ok((i, Expr::Number { value, pos }))
}

pub fn bool_lit_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, value) = boolean(input.clone())?;
    let pos = input.expand_until(&i);
    Ok((i, Expr::Boolean { value, pos }))
}

/// parses a slice expression `foo[0..43]`
///
/// asdf
pub fn slice_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    let (i, (p, e)) = pair(ident_expr, delimited(lbrack, range_expr, rbrack))(input)?;
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

/// parses a logical and (&&) expression
///
/// this expression evaluates to a boolean value
fn bool_land(input: TokenStream) -> IResult<TokenStream, Expr> {
    // we take the logical and (&&) of terms
    assert!(!input.is_empty());
    let (i, initial) = bool_unary_expr(input)?;

    let (i, remainder) = many0(|i: TokenStream| {
        let (i, add) = preceded(land, bool_unary_expr)(i)?;
        Ok((i, (BinOp::Land, add)))
    })(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

fn bool_unary_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    alt((
        bool_unary_lnot,
        bool_cmp_expr_arith,
        bool_cmp_expr_bool,
        bool_term_expr,
    ))(input)
}

/// parses a comparison expression
///
/// this expression evaluates to a boolean value
fn bool_cmp_expr_arith(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, lhs) = arith_expr(input)?;
    let (i, (op, rhs)) = alt((
        |i: TokenStream| {
            let (i, op) = preceded(eq, arith_expr)(i)?;
            Ok((i, (BinOp::Eq, op)))
        },
        |i: TokenStream| {
            let (i, op) = preceded(ne, arith_expr)(i)?;
            Ok((i, (BinOp::Ne, op)))
        },
        |i: TokenStream| {
            let (i, op) = preceded(gt, arith_expr)(i)?;
            Ok((i, (BinOp::Gt, op)))
        },
        |i: TokenStream| {
            let (i, op) = preceded(lt, arith_expr)(i)?;
            Ok((i, (BinOp::Lt, op)))
        },
        |i: TokenStream| {
            let (i, op) = preceded(le, arith_expr)(i)?;
            Ok((i, (BinOp::Le, op)))
        },
        |i: TokenStream| {
            let (i, op) = preceded(ge, arith_expr)(i)?;
            Ok((i, (BinOp::Ge, op)))
        },
    ))(i)?;
    let pos = lhs.loc().clone().merge(rhs.loc());
    Ok((
        i,
        Expr::BinaryOperation {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            pos,
        },
    ))
}

/// parses a comparison expression
///
/// this expression evaluates to a boolean value
fn bool_cmp_expr_bool(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, lhs) = bool_term_expr(input)?;
    let (i, (op, rhs)) = alt((
        |i: TokenStream| {
            let (i, op) = preceded(eq, bool_term_expr)(i)?;
            Ok((i, (BinOp::Eq, op)))
        },
        |i: TokenStream| {
            let (i, op) = preceded(ne, bool_term_expr)(i)?;
            Ok((i, (BinOp::Ne, op)))
        },
    ))(i)?;
    let pos = lhs.loc().clone().merge(rhs.loc());
    Ok((
        i,
        Expr::BinaryOperation {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            pos,
        },
    ))
}

/// parses a logical unary not (!) expression
fn bool_unary_lnot(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, v) = preceded(lnot, bool_term_expr)(input.clone())?;
    let pos = input.merge(v.loc());
    Ok((
        i,
        Expr::UnaryOperation {
            op: UnOp::LNot,
            val: Box::new(v),
            pos,
        },
    ))
}

/// parses an xor expression
///
/// an arithmetic expression that evaluates to a number (a ^ b)
fn arith_xor_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = arith_and_expr(input)?;

    let (i, remainder) = many0(|i: TokenStream| {
        let (i, op) = preceded(xor, arith_and_expr)(i)?;
        Ok((i, (BinOp::Or, op)))
    })(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

/// parses an xor expression
///
/// an arithmetic expression that evaluates to a number (a & b)
fn arith_and_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = arith_shift_expr(input)?;

    let (i, remainder) = many0(|i: TokenStream| {
        let (i, op) = preceded(and, arith_shift_expr)(i)?;
        Ok((i, (BinOp::And, op)))
    })(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

fn arith_shift_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = arith_add_expr(input)?;
    let (i, remainder) = many0(alt((
        |i: TokenStream| {
            let (i, op) = preceded(lshift, arith_add_expr)(i)?;
            Ok((i, (BinOp::LShift, op)))
        },
        |i: TokenStream| {
            let (i, op) = preceded(rshift, arith_add_expr)(i)?;
            Ok((i, (BinOp::RShift, op)))
        },
    )))(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

/// parses a + / -
fn arith_add_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = arit_mul_expr(input)?;
    let (i, remainder) = many0(alt((
        |i: TokenStream| {
            let (i, op) = preceded(plus, arit_mul_expr)(i)?;
            Ok((i, (BinOp::Plus, op)))
        },
        |i: TokenStream| {
            let (i, op) = preceded(minus, arit_mul_expr)(i)?;
            Ok((i, (BinOp::Minus, op)))
        },
    )))(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

/// parses a * / %
fn arit_mul_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, initial) = arith_unary_expr(input)?;
    let (i, remainder) = many0(alt((
        |i: TokenStream| {
            let (i, op) = preceded(star, arith_unary_expr)(i)?;
            Ok((i, (BinOp::Multiply, op)))
        },
        |i: TokenStream| {
            let (i, op) = preceded(slash, arith_unary_expr)(i)?;
            Ok((i, (BinOp::Divide, op)))
        },
        |i: TokenStream| {
            let (i, op) = preceded(percent, arith_unary_expr)(i)?;
            Ok((i, (BinOp::Modulo, op)))
        },
    )))(i)?;

    Ok((i, fold_exprs(initial, remainder)))
}

fn arith_unary_not(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, val) = preceded(not, arith_term_expr)(input.clone())?;
    let pos = input.merge(val.loc());
    Ok((
        i,
        Expr::UnaryOperation {
            op: UnOp::LNot,
            val: Box::new(val),
            pos,
        },
    ))
}

fn arith_unary_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    alt((arith_unary_not, arith_term_expr))(input)
}

fn ident_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, (fst, mut ot)) = pair(ident, many0(preceded(dot, ident)))(input.clone())?;
    let mut path = Vec::from([fst]);
    path.append(&mut ot);
    let pos = input.expand_until(&i);
    Ok((i, Expr::Identifier { path, pos }))
}

/// pares a function call expression `foo()`
///
/// This parses a function call without arguments
///
/// TODO: test support for arguments
fn fn_call_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    let (i, (e, args)) = pair(
        ident_expr,
        delimited(lparen, separated_list0(comma, expr), rparen),
    )(input)?;
    match e {
        Expr::Identifier { path, pos } => Ok((i, Expr::FnCall { path, args, pos })),
        _ => panic!("unexpected type"),
    }
}

/// parses a slice element expression `foo[3]`
///
/// this returns a single element from a slice
fn element_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    let (i, (p, e)) = pair(ident_expr, delimited(lbrack, num_lit_expr, rbrack))(input)?;
    match p {
        Expr::Identifier { path, pos } => Ok((
            i,
            Expr::Element {
                path,
                idx: Box::new(e),
                pos,
            },
        )),
        _ => panic!("unexpected type"),
    }
}

/// parses a logical term
///
/// This is either
///  - a boolean `true`
///  - a function call or element access `foo()` or `foo[1]`
///  - an identifier `abc`
///  - or another boolean expression in parentesis `(a && b)`
fn bool_term_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    alt((
        // it can be a boolean literal (true | false)
        bool_lit_expr,
        // a function call expression returning a boolean
        fn_call_expr,
        // element expression returning a boolean
        element_expr,
        // it can be a identifier (variable)
        ident_expr,
        // its a term in parenthesis
        preceded(lparen, terminated(bool_expr, cut(rparen))),
    ))(input)
}

/// parses an arithmetic term expression
///
/// This is either
///  - a number `123`
///  - a function call or element access `foo()` or `foo[1]`
///  - an identifier `abc`
///  - or another arithmetic expression in parentesis `(a + b)`
fn arith_term_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    alt((
        // try to parse a number
        num_lit_expr,
        // a function call expression returning an integer
        fn_call_expr,
        // element expression returning an integer
        element_expr,
        // try to parse an identifier
        ident_expr,
        // try to parse an `(arith_expr)`
        preceded(lparen, terminated(arith_expr, cut(rparen))),
    ))(input)
}

#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::nom::Slice;
#[cfg(test)]
use crate::sourcepos::SourcePos;
use nom::multi::separated_list0;

#[cfg(test)]
macro_rules! parse_equal (
    ($parser:expr, $lhs:expr, $rhs:expr) => (
        let sp = SourcePos::new("stdio", $lhs);
        let tokens = Lexer::lex_source_pos(sp).unwrap();
        let len = tokens.len();
        let ts = TokenStream::from_vec(tokens);
        assert_eq!(
            $parser(ts.clone()).map(|(i, x)| (i, format!("{}", x))),
            Ok((
                ts.slice(len - 1..len),
                String::from($rhs)
            ))
        );
    )
);

#[cfg(test)]
macro_rules! parse_fail(
    ($parser:expr, $lhs:expr) => (
        let sp = SourcePos::new("stdio", $lhs);
        let tokens = Lexer::lex_source_pos(sp).unwrap();
        let ts = TokenStream::from_vec(tokens);
        assert!(
            $parser(ts.clone()).is_err(),
        );
    )
);

#[test]
fn test_literals() {
    // some literals
    parse_equal!(expr, "1", "1");
    parse_equal!(expr, "true", "true");
    parse_equal!(expr, "ident", "ident");
    parse_equal!(expr, "ident.path.expr", "ident.path.expr");
    parse_equal!(expr, "(1)", "1");
    parse_equal!(expr, "foo[3]", "foo[3]");
    parse_equal!(expr, "bar()", "bar()");
    parse_equal!(expr, "foo.bar[3]", "foo.bar[3]");
    // unclosed
    parse_fail!(expr, "(1");
    parse_fail!(expr, "(1(");
}

#[test]
fn test_arithmetic() {
    // some arithmetic o
    parse_equal!(arith_expr, "1 + 2 * 3 + 4", "((1 + (2 * 3)) + 4)");
    parse_equal!(
        arith_expr,
        "1 + 2 * 3 + 4 << 5 * 2",
        "(((1 + (2 * 3)) + 4) << (5 * 2))"
    );
    parse_equal!(arith_expr, "1 + a + b + 4 + 5", "((((1 + a) + b) + 4) + 5)");
    parse_equal!(arith_expr, "a + 1 + b + 4 + 5", "((((a + 1) + b) + 4) + 5)");
    parse_equal!(arith_expr, "a + 1", "(a + 1)");

    parse_fail!(bool_expr, "1 + 2 * 3 + 4");
}

#[test]
fn test_boolean() {
    parse_equal!(
        bool_expr,
        "a && b || c && d || x > 9",
        "(((a && b) || (c && d)) || (x > 9))"
    );
    parse_equal!(
        bool_expr,
        "a.a && b.b || c.x && d.d.a || x > 9 && !zyw",
        "(((a.a && b.b) || (c.x && d.d.a)) || ((x > 9) && !(zyw)))"
    );
    parse_equal!(bool_expr, "a && b == true", "(a && (b == true))");
    parse_equal!(
        bool_expr,
        "s.x || a() && b() || c[3]",
        "((s.x || (a() && b())) || c[3])"
    );
    parse_equal!(
        bool_expr,
        "a && b && c || d || true",
        "((((a && b) && c) || d) || true)"
    );
    parse_equal!(bool_expr, "a < 123 && b > 432", "((a < 123) && (b > 432))");
    parse_equal!(bool_expr, "a == true", "(a == true)");
}

#[test]
fn test_range() {
    parse_equal!(range_expr, "a..b", "a..b");
    parse_equal!(range_expr, "1..2", "1..2");
    parse_equal! {
        range_expr,
        "a+b..1+5",
        "(a + b)..(1 + 5)"
    }
}

#[test]
fn test_slice() {
    parse_equal!(slice_expr, "foo[1..2]", "foo[1..2]");
    parse_equal!(slice_expr, "foo[a..len]", "foo[a..len]");
    parse_equal! {
        slice_expr,
        "foo[a+4..len-1]",
        "foo[(a + 4)..(len - 1)]"
    }
}

#[test]
// TODO: add function parser test
fn test_functions() {}
