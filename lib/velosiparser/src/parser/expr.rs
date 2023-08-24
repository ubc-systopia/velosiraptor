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

//! # VelosiParser: Expressions
//!
//! This module contains the parser for expressions.

// external dependencies
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
use crate::parser::{parameter::param, terminals::*};
use crate::parsetree::*;
use crate::{VelosiKeyword, VelosiTokenKind, VelosiTokenStream};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Notes on Operator Precedence
////////////////////////////////////////////////////////////////////////////////////////////////////

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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Expression Parsers (public exports)
////////////////////////////////////////////////////////////////////////////////////////////////////

/// parses an expression
///
/// This is the entry point into the expression parsing functionality. This parser recognizes any
/// syntactically valid expression starting from the weakest binding operator.
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `EXPR := IMPLIES_EXPR`
///
/// # Examples
///
///  * `a + b` (binary operation)
///  * `foo()` (function call)
///
pub fn expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    implies_expr(input)
}

/// parses a quantifier expression (forall & exists)
///
/// This expression evaluates to a boolean.
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `QUANTIFIER_EXPR := (KW_FORALL | KW_EXISTS) (IDENT COLON TYPE)+ PATHSEP EXPR
///
/// # Examples
///
///  * `forall x : int :: x > 0`
///  * `exists y : int :: y < 0
///
pub fn quantifier_expr(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let mut pos = input.clone();
    // try parse the keyword
    let (i2, quantifier) = alt((kw_exists, kw_forall))(input)?;
    // now we're in a quantifier, get the list of variables
    let (i3, vars) = cut(separated_list1(comma, param))(i2)?;

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

/// parses a range expression
///
/// The range expression is used to specify a range of values from a starting
/// value, up to but not including end value.
///
/// Currently, we only allow numeric literal expressions for the start and end values
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `RANGE_EXPR := NUM_LIT_EXPR .. NUM_LIT_EXPR`
///
/// # Examples
///
/// `0..10` corresponds to the mathematical interval `[0, 10)`
///
/// an arithmetic expression evalutes to a number a | b
pub fn range_expr(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeRangeExpr> {
    let mut pos = input.clone();
    let (i, (s, _, e)) = tuple((num_lit_expr, dotdot, num_lit_expr))(input)?;
    pos.span_until_start(&i);

    match (s, e) {
        (VelosiParseTreeExpr::NumLiteral(s), VelosiParseTreeExpr::NumLiteral(e)) => {
            let range = VelosiParseTreeRangeExpr::new(s.value, e.value, pos);
            Ok((i, range))
            //Ok((i, VelosiParseTreeExpr::Range(range)))
        }
        _ => unreachable!(),
    }
}

/// pares a function call expression
///
/// This may also be used to recognize function-call like expressions such as constructing a new
/// Unit type.
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `FN_CALL_EXPR := IDENT LPAREN LIST(COMMA, EXPR) RPAREN
///
/// # Examples
///
///  * `a()`
///  * `b(a)`
///
pub fn fn_call_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let mut pos = input.clone();
    let (i, id) = ident(input)?;

    let (i, args) = delimited(lparen, cut(separated_list0(comma, expr)), cut(rparen))(i)?;

    pos.span_until_start(&i);
    Ok((
        i,
        VelosiParseTreeExpr::FnCall(VelosiParseTreeFnCallExpr::new(id, args, pos)),
    ))
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper Functions and Macros
////////////////////////////////////////////////////////////////////////////////////////////////////

/// folds expressions into a tree
///
/// Converts a list of expressions with the same precedence into a tree of binary operations.
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
/// this constructs a binary operation parser for one or more operators with the same precedence.
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
//////
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized constant definition as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
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
                        let (i2, op) = preceded(unop_parse, cut($this))(i.clone())?;

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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Parsing Binary and Unary Operators with Precedence
////////////////////////////////////////////////////////////////////////////////////////////////////

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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Parsing Binary and Unary Operators with Precedence
////////////////////////////////////////////////////////////////////////////////////////////////////

/// parse a term expression
///
/// A term expression refers to an element of a binary expression or unary expression that itself
/// is not a binary or unary exprssion. Term expressions include literals, function calls,
/// identifiers, element accesses, range exprssions, and conditionals.
///
/// Moreover, expressions can be explicitly grouped using parenthesis. This is also recognized here.
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `TERM_EXPR := NUM_LIT_EXPR | BOOL_LIT_EXPR | FN_CALL_EXPR | ELEMENT_EXPR | IDENT_EXPR | LPAREN EXPR RPAREN
///
/// # Examples
///
/// * `1`
/// * `foo`
/// * `foo(1, 2)`
///
fn term_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
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
        // if-then-else expression
        if_else_expr,
        // it can be a identifier (variable)
        ident_expr,
        // a quantifier expression
        quantifier_expr,
        // its a term in parenthesis
        preceded(lparen, cut(terminated(expr, rparen))),
    ))(input)
}

/// parses an if-then-else expression
///
/// The if-then-else expression is used to specify a conditional expression, both branches must
/// be present.
///
/// Note, the parser does not enforce that the condition is a boolean expression and that the
/// two branches have the same type.
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `IF_THEN_ELSE := KW_IF EXPR LBRACE EXPR RBRACE KW_ELSE LBRACE EXPR RBRACE`
///
/// # Example
///
/// * `if 3 > a { 1 } else { 2 }`
///
fn if_else_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
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
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. This is a recoverable error indicating that the parser did
///        not recognize the input but another parser might.
///
/// # Grammar
///
/// `NUM := HEX_NUM | DEC_NUM | OCT_NUM | BIN_NUM`
///
/// # Example
///
/// * `1234`
/// * `0xabc`
///
fn num_lit_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
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
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. This is a recoverable error indicating that the parser did
///        not recognize the input but another parser might.
///
/// # Grammar
///
/// `BOOL := true | false
///
/// # Example
///
/// `true`, `false
fn bool_lit_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
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
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// SLICE_EXPR := IDENT_EXPR LBRACK RANGE_EXPR RBRACK
///
/// # Example
///
/// `foo[0..1]`
///
fn slice_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let mut pos = input.clone();
    let (i, (p, e)) = pair(ident_expr, delimited(lbrack, range_expr, cut(rbrack)))(input)?;
    pos.span_until_start(&i);

    Ok((
        i,
        VelosiParseTreeExpr::Slice(VelosiParseTreeSliceExpr::new(p, e, pos)),
    ))
}

/// parses an element access expression
///
/// This constructs a parser that recognizes an element access `foo[0]`.
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `ELEMENT_EXPR := IDENT_EXPR LBRACK NUM_LIT RBRACK`
///
/// # Example
///
///  * `foo[1]`
fn element_expr(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let mut pos = input.clone();
    let (i, (path, e)) = pair(ident_expr, delimited(lbrack, num_lit_expr, rbrack))(input)?;

    pos.span_until_start(&i);
    Ok((
        i,
        VelosiParseTreeExpr::Element(VelosiParseTreeElementExpr::new(path, e, pos)),
    ))
}

/// parses an identifier expression
///
/// This parser recognizes identifiers includingthe special keywords `state` and `interface`.
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized expression as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
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
    let mut pos = input.clone();
    // we need to match on the state and interface keywords as well,
    // so we are doing this manually here, try to take a single token
    let (rem, tok) = take(1usize)(input.clone())?;

    let fst = if let Some(t) = tok.peek() {
        match t.kind() {
            VelosiTokenKind::Keyword(VelosiKeyword::State) => String::from("state"),
            VelosiTokenKind::Keyword(VelosiKeyword::Interface) => String::from("interface"),
            VelosiTokenKind::Keyword(VelosiKeyword::StaticMapUnit) => String::from("staticmap"),
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
    let mut path = Vec::from([VelosiParseTreeIdentifier::new(fst, tok)]);
    path.append(&mut ot);

    pos.span_until_start(&i);

    Ok((
        i,
        VelosiParseTreeExpr::Identifier(VelosiParseTreeIdentifierLiteral::new(path, pos)),
    ))
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Testing
////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
use velosilexer::VelosiLexer;

#[cfg(test)]
use crate::{test_parse_and_check_fail, test_parse_and_compare_ok};

#[test]
fn test_literals() {
    test_parse_and_compare_ok!("1", expr);
    test_parse_and_compare_ok!("true", expr);
    test_parse_and_compare_ok!("ident", expr);
    test_parse_and_compare_ok!("ident.path.expr", expr);
    test_parse_and_compare_ok!("(1)", expr, "1");
}

#[test]
fn test_literals_fail() {
    test_parse_and_check_fail!("(1", expr);
    test_parse_and_check_fail!("(1(", expr);
    test_parse_and_check_fail!("ident.path.", expr);
}

#[test]
fn test_fncall() {
    test_parse_and_compare_ok!("bar()", expr);
    test_parse_and_compare_ok!("bar(123)", expr);
    test_parse_and_compare_ok!("bar(123, 456)", expr);
    test_parse_and_compare_ok!("bar(123, 456, foo(bar))", expr);
    test_parse_and_compare_ok!("bar(123, 456, foo(bar, 1234))", expr);
    test_parse_and_compare_ok!("bar(baz[3], 456, foo(bar, 1234))", expr);
}

#[test]
fn test_fncall_fail() {
    test_parse_and_check_fail!("bar(", expr);
    test_parse_and_check_fail!("bar(123]", expr);
}

#[test]
fn test_slice() {
    test_parse_and_compare_ok!("foo[3..4]", expr);
    test_parse_and_compare_ok!("foo.bar[0..3]", expr);
    test_parse_and_compare_ok!("foo[1..2]", slice_expr);

    // currently we don't support this
    test_parse_and_check_fail!("foo[1+2..1+2]", slice_expr);
    test_parse_and_check_fail!("foo[a..b]", slice_expr);
}

#[test]
fn test_element() {
    test_parse_and_compare_ok!("foo[3]", expr);
    test_parse_and_compare_ok!("foo.bar[3]", expr);

    // currently we don't support this
    test_parse_and_check_fail!("foo.bar[a]", expr);
    test_parse_and_check_fail!("foo.bar[a+1]", expr);
    test_parse_and_check_fail!("foo.bar[baz(3)]", expr);
    test_parse_and_check_fail!("foo.bar[bar.foo[3]]", expr);
}

#[test]
fn test_ifelse() {
    test_parse_and_compare_ok!("if true { 3 } else { 4 }", expr);
    test_parse_and_compare_ok!("if FOO { 3 } else { 4 }", expr);
    test_parse_and_compare_ok!("if foo() { bar() } else { baz() }", expr);

    test_parse_and_compare_ok!(
        "if foo() { if bar() { 3 } else { 4 } } else { baz() }",
        expr
    );
    // doesn't do type check, so that's ok
    test_parse_and_compare_ok!("if FOO + 3 { 3 } else { 4 }", expr);
}

#[test]
fn test_ifelse_fail() {
    test_parse_and_check_fail!("if true { 3 }", expr);
}

#[test]
fn test_range() {
    // parse_equal!(range_expr, "a..b", "a..b");
    test_parse_and_compare_ok!("1..2", range_expr);

    // currently we don't support this
    test_parse_and_check_fail!("a..b", range_expr);
    test_parse_and_check_fail!("1+2..a+2", range_expr);
}

#[test]
fn test_quantifier() {
    test_parse_and_compare_ok!("forall x: int :: x > 0", quantifier_expr);
    test_parse_and_compare_ok!("exists x: int :: x > 0", quantifier_expr);

    test_parse_and_compare_ok!(
        "forall x: int, y: size :: x > 0 && a < b",
        quantifier_expr,
        "forall x: int, y: size :: (x > 0) && (a < b)"
    );
    test_parse_and_compare_ok!(
        "exists x: int, y: size :: x > 0 && y < 0",
        quantifier_expr,
        "exists x: int, y: size :: (x > 0) && (y < 0)"
    );
}

#[test]
fn test_ops_same_precedence() {
    test_parse_and_compare_ok!("1 + 2 + 3", expr, "(1 + 2) + 3");
    test_parse_and_compare_ok!("1 + 2 - 3", expr, "(1 + 2) - 3");
    test_parse_and_compare_ok!("1 + 2 - 3 + 4", expr, "((1 + 2) - 3) + 4");

    test_parse_and_compare_ok!("1 << 2 >> 3", expr, "(1 << 2) >> 3");
    test_parse_and_compare_ok!("1 >> 2 << 3", expr, "(1 >> 2) << 3");

    test_parse_and_compare_ok!("1 && 2 && 3", expr, "(1 && 2) && 3");
    test_parse_and_compare_ok!("1 || 2 || 3", expr, "(1 || 2) || 3");

    test_parse_and_compare_ok!("1 & 2 & 3", expr, "(1 & 2) & 3");
    test_parse_and_compare_ok!("1 | 2 | 3", expr, "(1 | 2) | 3");

    test_parse_and_compare_ok!("~1", expr, "~(1)");
    test_parse_and_compare_ok!("~~1", expr, "~(~(1))");

    test_parse_and_compare_ok!("true == a", expr);
    test_parse_and_compare_ok!("a == true", expr);
}

#[test]
fn test_ops_parens() {
    test_parse_and_compare_ok!("1 + (2 + 3)", expr, "1 + (2 + 3)");
    test_parse_and_compare_ok!("1 + (2 + 3) + 4", expr, "(1 + (2 + 3)) + 4");
}

#[test]
fn test_ops_different_precedence() {
    test_parse_and_compare_ok!("1 + 2 * 3 + 4", expr, "(1 + (2 * 3)) + 4");
    test_parse_and_compare_ok!("1 + 2 + 3 * 4 + 5", expr, "((1 + 2) + (3 * 4)) + 5");

    test_parse_and_compare_ok!(
        "a && b && c || d || e && f",
        expr,
        "(((a && b) && c) || d) || (e && f)"
    );

    test_parse_and_compare_ok!(
        "a || b || c && d && e || f",
        expr,
        "((a || b) || ((c && d) && e)) || f"
    );

    test_parse_and_compare_ok!(
        "a == 1 && b == 2 || c == 3 && d != 4 && e > 5",
        expr,
        "((a == 1) && (b == 2)) || (((c == 3) && (d != 4)) && (e > 5))"
    );

    test_parse_and_compare_ok!(
        "a +1 == 1 && b- 2 == 2 || c * 2 + 2 == 3 && d << 3 != 4 && e << 4 * 4 > 5",
        expr,
        "(((a + 1) == 1) && ((b - 2) == 2)) || (((((c * 2) + 2) == 3) && ((d << 3) != 4)) && ((e << (4 * 4)) > 5))"
    );

    test_parse_and_compare_ok!(
        "a == b | c ^ d & e << f & g >> i",
        expr,
        "a == (b | (c ^ ((d & (e << f)) & (g >> i))))"
    );

    test_parse_and_compare_ok!("s.x || a() && b() || c", expr, "(s.x || (a() && b())) || c");

    test_parse_and_compare_ok!(
        "a.a && b.b || c.x && d.d.a || x > 9 && !zyw",
        expr,
        "((a.a && b.b) || (c.x && d.d.a)) || ((x > 9) && !(zyw))"
    );

    test_parse_and_compare_ok!(
        "a == ~b | c ^ d & ~e << f & g >> i",
        expr,
        "a == (~(b) | (c ^ ((d & (~(e) << f)) & (g >> i))))"
    );

    test_parse_and_compare_ok!("a ==> b || c ==> d", expr, "(a ==> (b || c)) ==> d");
}
