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
//!

// the used nom componets
use nom::{
    branch::alt,
    bytes::complete::take,
    combinator::{cut, fail, opt},
    multi::many0,
    multi::{separated_list0, separated_list1},
    sequence::{delimited, tuple},
    sequence::{pair, preceded, terminated},
    Err, Needed,
};

// lexer, parser terminals and ast
use crate::ast::{AstNode, BinOp, Expr, Quantifier, UnOp};
use crate::error::{IResult, VrsError};
use crate::parser::{param::parameter, terminals::*};
use crate::token::{Keyword, TokenContent, TokenStream};

// Precedence of Operators  (strong to weak)
// Operator                         Associativity       Example
// Paths                                                a::b
// Method calls                                         a.b()
// Field expressions                left to right       a.b.c
// Function calls, array indexing                       a()  a[1]
// ?                                                    ?
// Unary - * ! &                                        !a
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

/// folds expressions
///
/// convert a list of expressions with the same precedence into a tree
/// representation
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

/// builds a binary operator parser
///
/// this constructs a binary operation parser for one or more operators with the same
/// precedence.
/// The macro supports multiple `(op, parser)` tuples as arguments.
///
/// # Grammar
///
/// `THIS_EXPR  := NEXT_EXPR (OP NEXT_EXPR)*
///
/// # Example
///
/// * Logical Or expressions (a || b): `binop_parser!(lor_expr, land_expr, (BinOp::Lor, lor))`
///
macro_rules! binop_parser (
    ($this:ident, $next:ident, $( $optup:expr ),* ) => (
        fn $this(input: TokenStream) -> IResult<TokenStream, Expr> {
            // try to recognize at least one token of the next parser
            let (i, initial) = $next(input)?;
            // build the parser for one or more `OP NEXT_EXPR` parser
            let (i, remainder) = many0(alt((
                $(
                    |i: TokenStream| {
                        let (binop, binop_parse) = $optup;
                        // recognize the operator, fail on the next parser
                        let (i, op) = preceded(binop_parse, cut($next))(i)?;
                        Ok((i, (binop, op)))
                    },
                )*
                |i : TokenStream| {
                    // always fail as we could not recognize any of the supplied binops here
                    fail(i)
                }
            ))
            )(i)?;
            // all right, now fold the expressions, to bild the tree
            Ok((i, fold_exprs(initial, remainder)))
        }
    )
);

/// builds a unary operator parser
///
/// This constructs a unuary operator parser for one or more operators with the same precedence.
/// The unary oparator may or may not be present.
/// The macro supports multiple `(op, parser)` tuples as arguments.
///
/// # Grammar
///
/// `THIS_EXPR := OP NEXT_EXPR | NEXT_EXPR
///
/// # Example
///
///  * Logical Not expression (!a): `unop_parser!(unary_expr, term_expr, (UnOp::Not, not));`
///
macro_rules! unop_parser (
    ($this:ident, $next:ident, $( $optup:expr ),* ) => (
        fn $this(input: TokenStream) -> IResult<TokenStream, Expr> {
            alt((
                $(
                    |i: TokenStream| {
                        let (unop, unop_parse) = $optup;
                        // recognize the unary operator followed by the next parser
                        let (i2, op) = preceded(unop_parse, cut($next))(i.clone())?;
                        // expand the position until the end
                        let pos = i.expand_until(&i2);
                        Ok((
                            i2,
                            Expr::UnaryOperation {
                                op: unop,
                                val: Box::new(op),
                                pos
                            },
                        ))
                    },
                )*
                    |i : TokenStream| {
                        // the plain next parser without unary operator is the next
                        $next(i)
                    }
            ))(input)
        }
    )
);

/// builds a comparator expression parser
///
/// This constructs parsers for comparison operations with a left-hand size and right-hand size
///
/// # Grammar
///
/// `THIS_EXPR := NEXT_EXPR (OP NEXT_EXPR)?
///
/// # Example
///
/// * equality: `cmp_parser!(cmp_expr, or_expr, (BinOp::Eq, eq)`
macro_rules! cmp_parser (
    ($this:ident, $next:ident, $( $optup:expr ),* ) => (
        fn $this(input: TokenStream) -> IResult<TokenStream, Expr> {
            let (i, lhs) = $next(input)?;
            // take an option comparison operator here
            let (i, rhs) = opt(alt((
                $(
                |i: TokenStream| {
                    let (binop, binop_parse) = $optup;
                    let (i, op) = preceded(binop_parse, cut($next))(i)?;
                    Ok((i, (binop, op)))
                },
                )*
                |i : TokenStream| {
                    fail(i)
                }
            )))(i)?;
            match rhs {
                // we recognized the comparator
                Some((op, rhs)) => {
                    // position spans from LHS to RHS
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
                // no comparator, just return the lhs
                None => Ok((i, lhs))
            }
        }
    )
);

/// parses a quantifier expression
///
/// # Grammar
///
/// `QUANTIFIER_EXPR := KW_FORALL | KW_EXISTS (VARS)+ PathSep EXPR
/// `QUANTIFIER_EXPR := KW_FORALL | KW_EXISTS (VARS)+ PIPE EXPR PathSep EXPR.
///
/// # Example
///
/// forall x :: x > 0
///
pub fn quantifier_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    // try parse the keyword
    let (i2, quantifier) = alt((kw_exists, kw_forall))(input.clone())?;
    // now we're in a quantifier, get the list of variables
    let (i3, vars) = cut(separated_list1(comma, parameter))(i2)?;

    // then the `::` followed by an expression
    let (i4, expr) = cut(preceded(pathsep, bool_expr))(i3)?;

    // calculate the tokenstream
    let pos = input.expand_until(&i4);

    // get the quantifier
    let kind = match quantifier.peek().content {
        TokenContent::Keyword(Keyword::Forall) => Quantifier::Forall,
        TokenContent::Keyword(Keyword::Exists) => Quantifier::Exists,
        _ => panic!("should not happen!"),
    };

    Ok((
        i4,
        Expr::Quantifier {
            kind,
            vars,
            expr: Box::new(expr),
            pos,
        },
    ))
}

/// parses an expression
///
/// This is the entry point into the expression parsing functionality. This
/// parser recognizes any valid expression, but does not perform any type
/// checking.
///
pub fn expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    implies_expr(input)
}

/// parses an arithmetic expression
///
/// Currently this is just parsing a generic expression
///
pub fn arith_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    implies_expr(input)
}

/// parses a boolean expression
///
/// Currently this is just parsing a generic expression.
///
pub fn bool_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    implies_expr(input)
}

// ===>                               left to right
binop_parser!(implies_expr, lor_expr, (BinOp::Implies, rlongfatarrow));
// ||                               left to right
binop_parser!(lor_expr, land_expr, (BinOp::Lor, lor));
// &&                               left to right
binop_parser!(land_expr, cmp_expr, (BinOp::Land, land));
// == != < > <= >=                  Require parentheses
cmp_parser!(
    cmp_expr,
    or_expr,
    (BinOp::Eq, eq),
    (BinOp::Ne, ne),
    (BinOp::Gt, gt),
    (BinOp::Lt, lt),
    (BinOp::Le, le),
    (BinOp::Ge, ge)
);
// |                                left to right       a | b
binop_parser!(or_expr, xor_expr, (BinOp::Or, or));
// ^                                left to right       a * b
binop_parser!(xor_expr, and_expr, (BinOp::Xor, xor));
// &                                left to right       a & b
binop_parser!(and_expr, shift_expr, (BinOp::And, and));
// << >>                            left to right       a << b, a >> b,
binop_parser!(
    shift_expr,
    add_sub_expr,
    (BinOp::LShift, lshift),
    (BinOp::RShift, rshift)
);
// + -                              left to right       a + b, a - b
binop_parser!(
    add_sub_expr,
    mul_div_expr,
    (BinOp::Plus, plus),
    (BinOp::Minus, minus)
);
// * / %                            left to right       a * b, a / b, a % b
binop_parser!(
    mul_div_expr,
    unary_expr,
    (BinOp::Multiply, star),
    (BinOp::Divide, slash),
    (BinOp::Modulo, percent)
);

// Unary - * ! &                                         !a, *a, ^a
unop_parser!(
    unary_expr,
    term_expr,
    (UnOp::Not, not),
    (UnOp::Ref, and),
    (UnOp::LNot, lnot)
);

/// parse a term expression
///
/// This is an expression term including literals, function calls, element acesses,
/// identifiers, and `( expr )`.
///
/// # Grammar
///
/// `TERM_EXPR := NUM_LIT_EXPR | BOOL_LIT_EXPR | FN_CALL_EXPR | ELEMENT_EXPR | IDENT_EXPR | LPAREN EXPR RPAREN
pub fn term_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    alt((
        // try to parse a number
        num_lit_expr,
        // it can be a boolean literal (true | false)
        bool_lit_expr,
        // a function call expression returning a boolean
        fn_call_expr,
        // slice expression
        slice_expr,
        // element expression returning a boolean
        element_expr,
        // it can be a identifier (variable)
        ident_expr,
        // its a term in parenthesis
        preceded(lparen, cut(terminated(expr, rparen))),
    ))(input)
}

/// parses a range expression
///
/// The range expression is used to specify a range of values from a starting
/// value, up to but not including end value.
///
/// # Grammar
///
/// `RANGE_EXPR := ARITH_EXPR .. ARITH_EXPR`
///
/// # Example
///
/// `0..10` corresponds to the mathematical interval `[0, 10)`
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

/// parses a numeric literal
///
/// The numeric literal is a hexdecima, decimal, octal or binary number
///
/// # Grammar
///
/// `NUM := HEX_NUM | DEC_NUM | OCT_NUM | BIN_NUM`
///
/// # Example
///
/// `1234`, `0xabc`
///
pub fn num_lit_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, value) = num(input.clone())?;
    let pos = input.expand_until(&i);
    Ok((i, Expr::Number { value, pos }))
}

/// parses a boolean literal
///
/// This corresponds to true or false.
///
/// # Grammar
///
/// `BOOL := true | false
///
/// # Example
///
/// `true`, `false
pub fn bool_lit_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    assert!(!input.is_empty());
    let (i, value) = boolean(input.clone())?;
    let pos = input.expand_until(&i);
    Ok((i, Expr::Boolean { value, pos }))
}

/// parses a slice expression
///
/// The slice expression refers to range of elements within an array-like structure
///
/// # Grammar
///
/// SLICE_EXPR := IDENT_EXPR [ RANGE_EXPR ]
///
/// # Example
///
/// `foo[0..1]`
///
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

/// parses an identifier expression
///
/// This parser recognizes identifiers includingthe special keywords `state` and `interface`.
///
/// # Grammar
///
/// `IDENT_EXPR := (KW_STATE | KW_INTERFACE | IDENT) (DOT IDENT)*
///
/// # Example
///  * variable: `a`
///  * State reference: `state.a`
///
fn ident_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    // we need to match on the state and interface keywords as well,
    // so we are doing this manually here, try to take a single token
    let (rem, tok) = take(1usize)(input.clone())?;
    if tok.is_empty() {
        return Err(Err::Incomplete(Needed::new(1)));
    }

    // now check what we've got, either a keyword or one of
    let fst = match &tok.peek().content {
        TokenContent::Keyword(Keyword::State) => String::from("state"),
        TokenContent::Keyword(Keyword::Interface) => String::from("interface"),
        TokenContent::Identifier(s) => String::from(s),
        _ => {
            return Err(Err::Error(VrsError::from_token(
                input,
                TokenContent::Identifier(String::new()),
            )))
        }
    };
    // recognize the `.ident` parts
    let (i, mut ot) = many0(preceded(dot, ident))(rem)?;
    // merge the path into one big vector
    let mut path = Vec::from([fst]);
    path.append(&mut ot);
    let pos = input.expand_until(&i);
    Ok((i, Expr::Identifier { path, pos }))
}

/// parses an expression list
///
/// # Grammar
///
/// `EXPR_LIST := [ EXPR (COMMA EXPR)* ]?`
pub fn expr_list(input: TokenStream) -> IResult<TokenStream, Vec<Expr>> {
    separated_list0(comma, expr)(input)
}

/// pares a function call expression
///
/// This parser recognizes a function call expression.
///
/// # Grammar
///
/// `FN_CALL_EXPR := IDENT (DOT IDENT)* LPAREN LIST(COMMA, EXPR) RPAREN
///
/// # Example
///
///  * `a()`
///  * `b(a)`
///
fn fn_call_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    let (i, (path, args)) = pair(
        separated_list1(dot, ident),
        delimited(lparen, expr_list, rparen),
    )(input.clone())?;
    let pos = input.expand_until(&i);
    Ok((i, Expr::FnCall { path, args, pos }))
}

/// parses a slice element expression
///
/// This constructs a parser that recognizes an element access `foo[0]`.
///
/// # Grammar
///
/// `ELEMENT_EXPR := IDENT_EXPR LBRACK NUM_LIT RBRACK`
///
/// # Example
///
///  * `foo[1]`
fn element_expr(input: TokenStream) -> IResult<TokenStream, Expr> {
    let (i, (path, e)) = pair(
        separated_list1(dot, ident),
        delimited(lbrack, expr, rbrack),
    )(input.clone())?;
    let pos = input.expand_until(&i);
    Ok((
        i,
        Expr::Element {
            path,
            idx: Box::new(e),
            pos,
        },
    ))
}

#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::nom::Slice;
#[cfg(test)]
use crate::sourcepos::SourcePos;

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
    parse_equal!(expr, "foo.bar[0..3]", "foo.bar[0..3]");
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
}

#[test]
fn test_boolean() {
    parse_equal!(
        bool_expr,
        "a && b || c && d || x > 9",
        "(((a && b) || (c && d)) || (x > 9))"
    );

    parse_equal!(bool_expr, "a ==> b || c ==> d", "((a ==> (b || c)) ==> d)");

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
    parse_equal!(bool_expr, "true == a", "(true == a)");
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
