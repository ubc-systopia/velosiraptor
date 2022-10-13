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

//! # Constant Definitions

// external dependencies
use nom::{
    combinator::cut,
    sequence::{delimited, pair, terminated},
};

// used crate functionality
use crate::error::IResult;
use crate::parser::expr::expr;
use crate::parser::terminals::{assign, colon, ident, kw_const, semicolon, typeinfo};
use crate::parsetree::VelosiParseTreeConstDef;
use crate::VelosiTokenStream;

/// parses and consumes an constant definition
///
/// The constant definition assigns a name to a constant value.
///
/// # Grammar
///
/// CONST := KW_CONST IDENT COLON TYPE ASSIGN EXPR SEMICOLON;
///
/// # Results
///
///  * OK:       when the parser successfully recognizes the constant definition
///  * Error:    when the parse could not recognize the constant definition
///  * Failure:  when the parser recognizes the constant definition, but it was malformed
///
/// # Examples
///
/// `const FOO : int = 1234;`
///
pub fn constdef(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeConstDef> {
    let mut pos = input.clone();

    // parse the `const` keyword, return otherwise
    let (i1, _) = kw_const(input)?;

    // parse the type information `IDENT : TYPE =`
    let (i2, (ident, ti)) = cut(pair(ident, delimited(colon, typeinfo, assign)))(i1)?;

    // parse the expression `EXPR SEMICOLON`
    let (i3, valexpr) = cut(terminated(expr, semicolon))(i2)?;

    // create the token stream covering the entire const def
    pos.span_until_start(&i3);
    Ok((i3, VelosiParseTreeConstDef::new(ident, ti, valexpr, pos)))
}

#[cfg(test)]
use velosilexer::VelosiLexer;

#[test]
fn test_ok() {
    // corresponds to `0 16 foobar`

    let content = "const FOO : int = 1234;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let (_, res) = constdef(ts).unwrap();
    assert_eq!(res.to_string().as_str(), "const FOO : int = 1234;");

    let content = "const FOO : addr = 0x1200;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(constdef(ts).is_ok());

    let content = "const FOO : size = 0x1200;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(constdef(ts).is_ok());

    let content = "const FOO : bool = true;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(constdef(ts).is_ok());

    // wrong type, but should parse
    let content = "const FOO : size = true;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(constdef(ts).is_ok());

    // wrong type, but should parse
    let content = "const FOO : bool = 0x123;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(constdef(ts).is_ok());

    // wrong type, but should parse
    let content = "const FOO : addr = true;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(constdef(ts).is_ok());
}

#[test]
fn test_fails() {
    // no semicolon
    let content = "const FOO : int = 1234 asdf";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(constdef(ts).is_err());

    // cannot use keywords
    let content = "const FOO : int = int;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(constdef(ts).is_err());

    // no type
    let content = "const FOO  = true;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(constdef(ts).is_err());
}
