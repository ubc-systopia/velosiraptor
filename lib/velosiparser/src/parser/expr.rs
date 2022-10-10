// VelosiParser -- Parser for the VelosiRaptor specification language
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

//! VelosiParseTreeExpression Parsing
//!

// the used nom componets
use nom::{
    branch::alt,
    bytes::complete::take,
    combinator::{cut, opt}, // fail,
    multi::{many0, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, terminated, tuple},
    Err,
    Needed,
};

// used crate functionality
use crate::error::{IResult, VelosiParserErr};
use crate::parser::{param::parameter, terminals::*};
use crate::parsetree::expr::*;
use crate::{VelosiKeyword, VelosiTokenKind, VelosiTokenStream};

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
fn fold_exprs(
    initial: VelosiParseTreeExpr,
    remainder: Vec<(VelosiParseTreeBinOp, VelosiParseTreeExpr)>,
) -> VelosiParseTreeExpr {
    remainder.into_iter().fold(initial, |acc, tuple| {
        let (op, expr) = tuple;

        let pos = acc.loc().from_self_until_end(expr.loc());
        let binop = VelosiParseTreeBinOpExpr::new(acc, op, expr, pos);
        VelosiParseTreeExpr::BinOp(binop)
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
/// * Logical Or expressions (a || b): `binop_parser!(lor_expr, land_expr, (VelosiParseTreeBinOp::Lor, lor))`
///
macro_rules! binop_parser (
    ($this:ident, $next:ident, $( $optup:expr ),* ) => (
        fn $this(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
            // try to recognize at least one token of the next parser
            let (i, initial) = $next(input)?;
            // build the parser for one or more `OP NEXT_EXPR` parser
            let (i, remainder) = many0(alt((
                $(
                    |i: VelosiTokenStream| {
                        let (binop, binop_parse) = $optup;
                        // recognize the operator, fail on the next parser
                        let (i, op) = preceded(binop_parse, cut($next))(i)?;
                        Ok((i, (binop, op)))
                    },
                )*
                // |i : VelosiTokenStream| {
                //     // always fail as we could not recognize any of the supplied binops here
                //     fail(i)
                // }
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
///  * Logical Not expression (!a): `unop_parser!(unary_expr, term_expr, (VelosiParseTreeUnOp::Not, not));`
///
macro_rules! unop_parser (
    ($this:ident, $next:ident, $( $optup:expr ),* ) => (
        fn $this(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
            alt((
                $(
                    |i: VelosiTokenStream| {
                        let mut pos = i.clone();

                        let (unop, unop_parse) = $optup;
                        let (i2, op) = preceded(unop_parse, cut($next))(i.clone())?;

                        // expand the position until the end
                        pos.span_until_start(&i2);

                        let unop = VelosiParseTreeUnOpExpr::new(unop, op, pos);
                        Ok((i2, VelosiParseTreeExpr::UnOp(unop)))
                    },
                )*
                    |i : VelosiTokenStream| {
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
/// * equality: `cmp_parser!(cmp_expr, or_expr, (VelosiParseTreeBinOp::Eq, eq)`
macro_rules! cmp_parser (
    ($this:ident, $next:ident, $( $optup:expr ),* ) => (
        fn $this(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
            let (i, lhs) = $next(input)?;
            // take an option comparison operator here
            let (i, rhs) = opt(alt((
                $(
                |i: VelosiTokenStream| {
                    let (binop, binop_parse) = $optup;
                    let (i, op) = preceded(binop_parse, cut($next))(i)?;
                    Ok((i, (binop, op)))
                },
                )*
                // |i : VelosiTokenStream| {
                //     fail(i)
                // }
            )))(i)?;
            match rhs {
                // we recognized the comparator
                Some((op, rhs)) => {
                    // position spans from LHS to RHS
                    let pos = lhs.loc().from_self_until_end(rhs.loc());
                    let binop = VelosiParseTreeBinOpExpr::new(lhs, op, rhs, pos);
                    Ok((i, VelosiParseTreeExpr::BinOp(binop)))
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
pub fn quantifier_expr(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let mut pos = input.clone();
    // try parse the keyword
    let (i2, quantifier) = alt((kw_exists, kw_forall))(input)?;
    // now we're in a quantifier, get the list of variables
    let (i3, vars) = cut(separated_list1(comma, parameter))(i2)?;

    // then the `::` followed by an expression
    let (i4, expr) = cut(preceded(coloncolon, expr))(i3)?;

    // get the quantifier
    let kind = match quantifier {
        VelosiKeyword::Forall => VelosiParseTreeQuantifier::Forall,
        VelosiKeyword::Exists => VelosiParseTreeQuantifier::Exists,
        _ => unreachable!(),
    };

    pos.span_until_start(&i4);
    let binop = VelosiParseTreeQuantifierExpr::new(kind, vars, expr, pos);
    Ok((i4, VelosiParseTreeExpr::Quantifier(binop)))
}

/// parses an expression
///
/// This is the entry point into the expression parsing functionality. This
/// parser recognizes any valid expression, but does not perform any type
/// checking.
///
pub fn expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    implies_expr(input)
}

// ===>                               left to right
binop_parser!(
    implies_expr,
    lor_expr,
    (VelosiParseTreeBinOp::Implies, rlongfatarrow)
);
// ||                               left to right
binop_parser!(lor_expr, land_expr, (VelosiParseTreeBinOp::Lor, lor));
// &&                               left to right
binop_parser!(land_expr, cmp_expr, (VelosiParseTreeBinOp::Land, land));
// == != < > <= >=                  Require parentheses
cmp_parser!(
    cmp_expr,
    or_expr,
    (VelosiParseTreeBinOp::Eq, eq),
    (VelosiParseTreeBinOp::Ne, ne),
    (VelosiParseTreeBinOp::Gt, gt),
    (VelosiParseTreeBinOp::Lt, lt),
    (VelosiParseTreeBinOp::Le, le),
    (VelosiParseTreeBinOp::Ge, ge)
);
// |                                left to right       a | b
binop_parser!(or_expr, xor_expr, (VelosiParseTreeBinOp::Or, or));
// ^                                left to right       a * b
binop_parser!(xor_expr, and_expr, (VelosiParseTreeBinOp::Xor, xor));
// &                                left to right       a & b
binop_parser!(and_expr, shift_expr, (VelosiParseTreeBinOp::And, and));
// << >>                            left to right       a << b, a >> b,
binop_parser!(
    shift_expr,
    add_sub_expr,
    (VelosiParseTreeBinOp::LShift, lshift),
    (VelosiParseTreeBinOp::RShift, rshift)
);
// + -                              left to right       a + b, a - b
binop_parser!(
    add_sub_expr,
    mul_div_expr,
    (VelosiParseTreeBinOp::Plus, plus),
    (VelosiParseTreeBinOp::Minus, minus)
);
// * / %                            left to right       a * b, a / b, a % b
binop_parser!(
    mul_div_expr,
    unary_expr,
    (VelosiParseTreeBinOp::Multiply, star),
    (VelosiParseTreeBinOp::Divide, slash),
    (VelosiParseTreeBinOp::Modulo, percent)
);

// Unary - * ! &                                         !a, *a, ^a
unop_parser!(
    unary_expr,
    term_expr,
    (VelosiParseTreeUnOp::Not, not),
    //(VelosiParseTreeUnOp::Ref, and),
    (VelosiParseTreeUnOp::LNot, lnot)
);

/// parse a term expression
///
/// This is an expression term including literals, function calls, element acesses,
/// identifiers, and `( expr )`.
///
/// # Grammar
///
/// `TERM_EXPR := NUM_LIT_EXPR | BOOL_LIT_EXPR | FN_CALL_EXPR | ELEMENT_EXPR | IDENT_EXPR | LPAREN EXPR RPAREN
pub fn term_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
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
        // element_expr,
        // if-then-else expression
        if_else_expr,
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
pub fn range_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let mut pos = input.clone();
    let (i, (s, _, e)) = tuple((num_lit_expr, dotdot, num_lit_expr))(input)?;
    pos.span_until_start(&i);

    match (s, e) {
        (VelosiParseTreeExpr::NumLiteral(s), VelosiParseTreeExpr::NumLiteral(e)) => {
            let range = VelosiParseTreeRangeExpr::new(s.value, e.value, pos);
            Ok((i, VelosiParseTreeExpr::Range(range)))
        }
        _ => unreachable!(),
    }
}

/// parses an if-then-else expression
///
/// The if then else expression is used to specify a conditional expression, both branches must
/// be present
///
/// # Grammar
///
/// `IF_THEN_ELSE := KW_IF EXPR LBRACE EXPR RBRACE KW_ELSE LBRACE EXPR RBRACE`
///
/// # Example
///
/// `if 3 > a { 1 } else { 2 }`
///
pub fn if_else_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let mut pos = input.clone();

    let (i1, _) = kw_if(input)?;
    let (i2, cond) = cut(expr)(i1)?;
    let (i3, then) = cut(delimited(lbrace, expr, rbrace))(i2)?;
    let (i4, _) = cut(kw_else)(i3)?;
    let (i5, other) = cut(delimited(lbrace, expr, rbrace))(i4)?;
    pos.span_until_start(&i5);
    Ok((
        i5,
        VelosiParseTreeExpr::IfElse(VelosiParseTreeIfElseExpr::new(cond, then, other, pos)),
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
pub fn num_lit_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let mut pos = input.clone();
    let (i, n) = num(input)?;
    pos.span_until_start(&i);
    Ok((
        i,
        VelosiParseTreeExpr::NumLiteral(VelosiParseTreeNumLiteral::new(n, pos)),
    ))
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
pub fn bool_lit_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let mut pos = input.clone();
    let (i, n) = boolean(input)?;
    pos.span_until_start(&i);
    Ok((
        i,
        VelosiParseTreeExpr::BoolLiteral(VelosiParseTreeBoolLiteral::new(n, pos)),
    ))
}

/// parses a slice expression
///
/// The slice expression refers to range of elements within an array-like structure
///
/// # Grammar
///
/// SLICE_EXPR := IDENT_EXPR LBRACK RANGE_EXPR RBRACK
///
/// # Example
///
/// `foo[0..1]`
///
pub fn slice_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let mut pos = input.clone();
    let (i, (p, e)) = pair(ident_path, delimited(lbrack, cut(range_expr), cut(rbrack)))(input)?;
    pos.span_until_start(&i);

    if let VelosiParseTreeExpr::Range(r) = e {
        Ok((
            i,
            VelosiParseTreeExpr::Slice(VelosiParseTreeSliceExpr::new(p, r, pos)),
        ))
    } else {
        unreachable!()
    }
}

fn ident_path(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeIdentifierLiteral> {
    let mut pos = input.clone();
    // we need to match on the state and interface keywords as well,
    // so we are doing this manually here, try to take a single token
    let (rem, tok) = take(1usize)(input.clone())?;

    let fst = if let Some(t) = tok.peek() {
        match t.kind() {
            VelosiTokenKind::Keyword(VelosiKeyword::State) => String::from("state"),
            VelosiTokenKind::Keyword(VelosiKeyword::Interface) => String::from("interface"),
            VelosiTokenKind::Keyword(VelosiKeyword::StaticMap) => String::from("staticmap"),
            VelosiTokenKind::Identifier(s) => String::from(s),
            _ => {
                let err = VelosiParserErr::from_expected(
                    input.from_self_with_subrange(0..1),
                    VelosiTokenKind::Identifier(String::new()),
                );
                return Err(Err::Error(err));
            }
        }
    } else {
        return Err(Err::Incomplete(Needed::new(1)));
    };

    // recognize the `.ident` parts
    let (i, mut ot) = many0(preceded(dot, cut(ident)))(rem)?;
    // merge the path into one big vector
    let mut path = Vec::from([fst]);
    path.append(&mut ot);

    pos.span_until_start(&i);

    Ok((i, VelosiParseTreeIdentifierLiteral::new(path, pos)))
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
fn ident_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let (i, id) = ident_path(input)?;
    Ok((i, VelosiParseTreeExpr::Identifier(id)))
}

/// parses an expression list
///
/// # Grammar
///
/// `EXPR_LIST := [ EXPR (COMMA EXPR)* ]?`
pub fn expr_list(input: VelosiTokenStream) -> IResult<VelosiTokenStream, Vec<VelosiParseTreeExpr>> {
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
///  * `a.b(c)`
///
fn fn_call_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let mut pos = input.clone();
    let (i, id) = ident_path(input)?;

    let (i, args) = delimited(lparen, cut(expr_list), cut(rparen))(i)?;

    pos.span_until_start(&i);
    let expr = VelosiParseTreeFnCallExpr::new(id, args, pos);
    Ok((i, VelosiParseTreeExpr::FnCall(expr)))
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
// fn element_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
//     let (i, (path, e)) =
//         pair(separated_list1(dot, ident), delimited(lbrack, expr, rbrack))(input.clone())?;
//     let pos = input.expand_until(&i);
//     Ok((
//         i,
//         VelosiParseTreeExpr::Element {
//             path,
//             idx: Box::new(e),
//             pos,
//         },
//     ))
// }

#[cfg(test)]
use velosilexer::VelosiLexer;

#[cfg(test)]
macro_rules! parse_equal (
    ($parser:expr, $lhs:expr, $rhs:expr) => (
        let ts = VelosiLexer::lex_string($lhs.to_string()).unwrap();
        let (_, res) = $parser(ts).unwrap();
        assert_eq!(
            res.to_string().as_str(),
            $rhs
        );
    )
);

#[cfg(test)]
macro_rules! parse_fail(
    ($parser:expr, $lhs:expr) => (
        let ts = VelosiLexer::lex_string($lhs.to_string()).unwrap();
        let res = $parser(ts);
        assert!(res.is_err(),);
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
    //parse_equal!(expr, "foo[3]", "foo[3]");
    parse_equal!(expr, "foo[3..4]", "foo[3..4]");
    parse_equal!(expr, "bar()", "bar()");
    //parse_equal!(expr, "foo.bar[3]", "foo.bar[3]");
    parse_equal!(expr, "foo.bar[0..3]", "foo.bar[0..3]");
    // unclosed
    parse_fail!(expr, "(1");
    parse_fail!(expr, "(1(");
}

#[test]
fn test_arithmetic() {
    // some arithmetic o
    parse_equal!(expr, "1 + 2 * 3 + 4", "((1 + (2 * 3)) + 4)");
    parse_equal!(
        expr,
        "1 + 2 * 3 + 4 << 5 * 2",
        "(((1 + (2 * 3)) + 4) << (5 * 2))"
    );
    parse_equal!(expr, "1 + a + b + 4 + 5", "((((1 + a) + b) + 4) + 5)");
    parse_equal!(expr, "a + 1 + b + 4 + 5", "((((a + 1) + b) + 4) + 5)");
    parse_equal!(expr, "a + 1", "(a + 1)");
}

#[test]
fn test_boolean() {
    parse_equal!(
        expr,
        "a && b || c && d || x > 9",
        "(((a && b) || (c && d)) || (x > 9))"
    );

    parse_equal!(expr, "a ==> b || c ==> d", "((a ==> (b || c)) ==> d)");

    parse_equal!(
        expr,
        "a.a && b.b || c.x && d.d.a || x > 9 && !zyw",
        "(((a.a && b.b) || (c.x && d.d.a)) || ((x > 9) && !(zyw)))"
    );
    parse_equal!(expr, "a && b == true", "(a && (b == true))");
    parse_equal!(
        expr,
        "s.x || a() && b() || c",
        "((s.x || (a() && b())) || c)"
    );
    parse_equal!(
        expr,
        "a && b && c || d || true",
        "((((a && b) && c) || d) || true)"
    );
    parse_equal!(expr, "a < 123 && b > 432", "((a < 123) && (b > 432))");
    parse_equal!(expr, "true == a", "(true == a)");
    parse_equal!(expr, "a == true", "(a == true)");
}

#[test]
fn test_range() {
    // parse_equal!(range_expr, "a..b", "a..b");
    parse_equal!(range_expr, "1..2", "1..2");
    // parse_equal! {
    //     range_expr,
    //     "a+b..1+5",
    //     "(a + b)..(1 + 5)"
    // }
}

#[test]
fn test_slice() {
    parse_equal!(slice_expr, "foo[1..2]", "foo[1..2]");
    // parse_equal!(slice_expr, "foo[a..len]", "foo[a..len]");
    // parse_equal! {
    //     slice_expr,
    //     "foo[a+4..len-1]",
    //     "foo[(a + 4)..(len - 1)]"
    // }
}

#[test]
fn test_fncall() {
    parse_equal!(expr, "bar(123)", "bar(123)");
}
