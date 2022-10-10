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

//! Method parsing

// the used nom functions
use nom::{
    branch::alt,
    combinator::{cut, opt},
    multi::{many0, separated_list0},
    sequence::{delimited, preceded, terminated},
};

// library internal includes
use crate::error::IResult;
use crate::parser::{
    expr::{expr, quantifier_expr},
    param::parameter,
    terminals::{
        comma, ident, kw_fn, kw_requires, lbrace, lparen, rarrow, rbrace, rparen, semicolon,
        typeinfo,
    },
};
use crate::parsetree::{
    VelosiParseTreeExpr, VelosiParseTreeMethod, VelosiParseTreeParam, VelosiParseTreeUnitNode,
};
use crate::VelosiTokenStream;

/// Parses a require clause
///
/// This adds a pre-condition to the function/method
///
/// # Grammar
///
/// `REQUIRE := KW_REQUIRES BOOL_EXPR;`
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
///
pub fn require_clauses(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    let (i1, _) = kw_requires(input)?;
    cut(terminated(alt((quantifier_expr, expr)), semicolon))(i1)
}

/// Parses a ensures clause
///
/// This adds a post-condition to the function/method.
///
/// # Grammar
///
/// `ENSURES := KW_ENSURES BOOL_EXPR;`
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
///
// pub fn ensure_clauses(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
//     let (i1, _) = kw_ensures(input)?;
//     cut(terminated(alt((quantifier_expr, expr)), semicolon))(i1)
// }

/// parses the method body
///
/// This parses the statements in the method body.
/// The method body must have at least one statement.
///
/// # Grammar
///
/// FN_BODY := { STMT+ }
///
/// # Results
///
///  * OK:      the parser could successfully recognize the method body
///  * Error:   the parser could not recognize the method body
///  * Failure: the parser recognized the method body, but it did not properly parse
///
/// # Examples
///
/// `{ return 0; }`
///
/// # TODO: is this just a statement block?
///
fn method_body(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeExpr> {
    delimited(lbrace, expr, cut(rbrace))(input)
}

/// parses an arguments list
///
/// This function parses a list of arguments with types annotations
///
/// # Grammar
///
/// ARG     := IDENT : TYPE
/// ARGLIST := (ARG | ARG (, ARG)+ )
///
/// # Results
///
///  * OK:      the parser could successfully recognize the arglist
///  * Error:   the parser could not recognize the arglist
///  * Failure: the parser recognized the arglist, but it did not properly parse
///
/// # Examples
///
/// `a : bool, b : int`
///
fn param_list(input: VelosiTokenStream) -> IResult<VelosiTokenStream, Vec<VelosiParseTreeParam>> {
    separated_list0(comma, parameter)(input)
}

/// parses a method definition
///
/// This function parses a full method definition.
///
/// # Grammar
///
/// METHOD := KW_FN IDENT ( ARGLIST ) -> TYPE REQUIRES+ ENSURES+ METHOD_BODY
///
/// # Results
///
///  * OK:      the parser could successfully recognize the method definition
///  * Error:   the parser could not recognize the method definition
///  * Failure: the parser recognized the method definition, but it did not properly parse
///
/// # Examples
///
/// `fn foo() -> addr`
///
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
pub fn method(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    // parse and consume fn keyword
    let (i1, _) = kw_fn(input)?;

    // get the method identifier, fail if there is not an identifier
    let (i2, name) = cut(ident)(i1)?;

    // arguments `LPAREN ARGLIST RPAREN`, fail on missing parenstheses
    let (i3, params) = delimited(cut(lparen), param_list, cut(rparen))(i2)?;

    // get the return type `-> Type`, fail if there is no arrow, or type info
    let (i4, rettype) = cut(preceded(rarrow, typeinfo))(i3)?;

    // get the ensures / requires clauses
    //let (i5, (requires, ensures)) = tuple((many0(require_clauses), many0(ensure_clauses)))(i4)?;
    let (i5, requires) = many0(require_clauses)(i4)?;

    // try to parse the method body
    let (i6, body) = opt(method_body)(i5)?;

    // create the token stream covering the entire method def
    pos.span_until_start(&i6);

    let method = VelosiParseTreeMethod {
        name,
        params,
        rettype,
        requires,
        // ensures,
        body,
        pos,
    };
    Ok((i6, VelosiParseTreeUnitNode::Method(method)))
}

#[cfg(test)]
use velosilexer::VelosiLexer;

#[test]
fn test_abstract() {
    let content = "fn foo() -> addr;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(method(ts).is_ok());

    let content = "fn foo(a : addr) -> addr;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(method(ts).is_ok());
}

#[test]
fn test_fail() {
    let content = "fn foo();";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(method(ts).is_err());

    let content = "fn foo(a) -> Addr;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(method(ts).is_err());
}

#[test]
fn test_ok() {
    let content = "fn foo() -> Addr {}";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(method(ts).is_ok());

    let content = "fn foo() -> addr { 3 }";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(method(ts).is_ok());

    let content = "fn foo() -> addr requires x > 0; ensures y < 3; { let x : int = 3; }";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(method(ts).is_ok());
}

// #[test]
// fn test_ok2() {
//     let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
//     d.push("tests/parser");

//     for f in vec!["methods.vrs"] {
//         d.push(f);
//         let filename = format!("{}", d.display());

//         // lex the file
//         let tokens = Lexer::lex_file(&filename);
//         assert!(tokens.is_ok());

//         let ts = VelosiTokenStream::from_vec_filtered(tokens.unwrap().0);
//         let res = many1(method)(ts);

//         println!("{:?}", res);

//         let (res, x) = res.unwrap();

//         println!("{}", res);
//         println!("{:?}", x);

//         // consumed all, but the EOF token
//         assert!(res.is_eof());

//         d.pop();
//     }
// }
