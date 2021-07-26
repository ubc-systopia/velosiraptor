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

//! Constants Definition Parsing

// nom parser combinators
use nom::{
    combinator::cut,
    sequence::{delimited, pair, terminated},
};

// lexer / parser imports
use crate::ast::{Const, Type};
use crate::error::IResult;
use crate::parser::expression::{arith_expr, bool_expr};
use crate::parser::terminals::{assign, colon, ident, kw_const, semicolon, typeinfo};
use crate::token::TokenStream;

/// parses a constat item of a unit
///
/// `const IDENT : TYPE = 123;`
pub fn constdef(input: TokenStream) -> IResult<TokenStream, Const> {
    // parse the `const` keyword, return otherwise
    let (i1, _) = kw_const(input.clone())?;

    // parse tye type information `IDENT : TYPE =`
    let (i2, (id, ti)) = cut(pair(ident, delimited(colon, typeinfo, assign)))(i1)?;

    // parse a numeric literal for now. TODO: make this a constant expression
    let (i3, value) = match ti {
        Type::Boolean => cut(terminated(bool_expr, semicolon))(i2),
        _ => cut(terminated(arith_expr, semicolon))(i2),
    }?;

    // create the token stream covering the entire const def
    let pos = input.expand_until(&i3);
    match ti {
        Type::Boolean => Ok((
            i3,
            Const::Boolean {
                ident: id,
                value,
                pos,
            },
        )),
        _ => Ok((
            i3,
            Const::Integer {
                ident: id,
                value,
                pos,
            },
        )),
    }
}

#[cfg(test)]
use crate::ast::Expr;
#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::sourcepos::SourcePos;

#[cfg(test)]
use nom::Slice;

#[test]
fn test_ok() {
    // corresponds to `0 16 foobar`
    let sp = SourcePos::new("stdio", "const FOO : int = 1234;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    let ts = TokenStream::from_vec(tokens);

    assert_eq!(
        constdef(ts.clone()),
        Ok((
            ts.slice(7..8),
            Const::Integer {
                ident: "FOO".to_string(),
                value: Expr::Number {
                    value: 1234,
                    pos: ts.slice(5..6)
                },
                pos: ts.slice(0..7)
            }
        ))
    );

    let sp = SourcePos::new("stdio", "const FOO : addr = 0x1200;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    assert!(constdef(TokenStream::from_vec(tokens)).is_ok());

    let sp = SourcePos::new("stdio", "const FOO : size = 0x1200;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    assert!(constdef(TokenStream::from_vec(tokens)).is_ok());

    let sp = SourcePos::new("stdio", "const FOO : bool = true;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    assert!(constdef(TokenStream::from_vec(tokens)).is_ok());
}

#[test]
fn test_fails() {
    // no semicolon
    let sp = SourcePos::new("stdio", "const FOO : int = 1234 asdf");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    assert!(constdef(TokenStream::from_vec(tokens)).is_err());

    // cannot use identifiers, we can if the other is a constant
    // let sp = SourcePos::new("stdio", "const FOO : int= asdf;");
    // let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    // assert!(constdef(TokenStream::from_vec(tokens)).is_err());

    // cannot use keywords
    let sp = SourcePos::new("stdio", "const FOO : int = int;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    assert!(constdef(TokenStream::from_vec(tokens)).is_err());

    // no type
    let sp = SourcePos::new("stdio", "const FOO  = true;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    assert!(constdef(TokenStream::from_vec(tokens)).is_err());

    // wrong type
    let sp = SourcePos::new("stdio", "const FOO : size = true;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    assert!(constdef(TokenStream::from_vec(tokens)).is_err());

    // wrong type
    let sp = SourcePos::new("stdio", "const FOO : bool = 0x123;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    assert!(constdef(TokenStream::from_vec(tokens)).is_err());

    // wrong type
    let sp = SourcePos::new("stdio", "const FOO : addr = true;");
    let tokens = Lexer::lex_source_pos(sp.clone()).unwrap();
    assert!(constdef(TokenStream::from_vec(tokens)).is_err());
}
