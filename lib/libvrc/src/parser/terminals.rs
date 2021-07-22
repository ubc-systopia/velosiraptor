// Velosiraptor Lexer
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

// NOM parsing constructs
use nom::{take, try_parse};
// NOM results
use nom::{Err, Needed};

use crate::ast::Type;
use crate::error::{IResult, VrsError};
use crate::token::{Keyword, TokenContent, TokenStream};

macro_rules! terminalparser (
    ($vis:vis $name:ident, $tag: expr) => (
        $vis fn $name(input: TokenStream) -> IResult<TokenStream, ()> {
            let (rem, tok) = try_parse!(input.clone(), take!(1));
            // we need at least one token
            if tok.is_empty() {
                Err(Err::Incomplete(Needed::new(1)))
            } else {
                if tok.peek().content == $tag {
                    Ok((rem, ()))
                } else {
                    Err(Err::Error(VrsError::from_token(input, $tag)))
                }
            }
        }
    )
);

// delimiters
terminalparser!(pub lparen, TokenContent::LParen);
terminalparser!(pub rparen, TokenContent::RParen);
terminalparser!(pub lbrace, TokenContent::LBrace);
terminalparser!(pub rbrace, TokenContent::RBrace);
terminalparser!(pub lbrack, TokenContent::LBracket);
terminalparser!(pub rbrack, TokenContent::RBracket);

// punctuations
terminalparser!(pub dot, TokenContent::Dot);
terminalparser!(pub comma, TokenContent::Comma);
terminalparser!(pub colon, TokenContent::Colon);
terminalparser!(pub semicolon, TokenContent::SemiColon);

// operators
terminalparser!(pub plus, TokenContent::Plus);
terminalparser!(pub minus, TokenContent::Minus);
terminalparser!(pub star, TokenContent::Star);
terminalparser!(pub slash, TokenContent::Slash);
terminalparser!(pub percent, TokenContent::Percent);

// shifts
terminalparser!(pub lshift, TokenContent::LShift);
terminalparser!(pub rshift, TokenContent::RShift);

// bitwise operators
terminalparser!(pub not, TokenContent::Not);
terminalparser!(pub and, TokenContent::And);
terminalparser!(pub or, TokenContent::Or);
terminalparser!(pub xor, TokenContent::Xor);

// logical operators
terminalparser!(pub lnot, TokenContent::LNot);
terminalparser!(pub land, TokenContent::LAnd);
terminalparser!(pub lor, TokenContent::LOr);

// comparators
terminalparser!(pub eq, TokenContent::Eq);
terminalparser!(pub ne, TokenContent::Ne);
terminalparser!(pub le, TokenContent::Le);
terminalparser!(pub ge, TokenContent::Ge);
terminalparser!(pub lt, TokenContent::Lt);
terminalparser!(pub gt, TokenContent::Gt);

// assignment
terminalparser!(pub assign, TokenContent::Assign);

// arrows
terminalparser!(pub fatarrow, TokenContent::FatArrow);
terminalparser!(pub rarrow, TokenContent::RArrow);

// comparators
terminalparser!(pub at, TokenContent::At);
terminalparser!(pub underscore, TokenContent::Underscore);
terminalparser!(pub dotdot, TokenContent::DotDot);
terminalparser!(pub pathsep, TokenContent::PathSep);
terminalparser!(pub wildcard, TokenContent::Wildcard);
terminalparser!(pub eof, TokenContent::Eof);

pub fn ident(input: TokenStream) -> IResult<TokenStream, String> {
    let (rem, tok) = try_parse!(input.clone(), take!(1));
    // we need at least one token
    if tok.is_empty() {
        Err(Err::Incomplete(Needed::new(1)))
    } else {
        let id = tok.peek();
        match &id.content {
            TokenContent::Identifier(s) => Ok((rem, s.clone())),
            _ => Err(Err::Error(VrsError::from_token(
                input,
                TokenContent::Identifier(String::new()),
            ))),
        }
    }
}

pub fn num(input: TokenStream) -> IResult<TokenStream, u64> {
    let (rem, tok) = try_parse!(input.clone(), take!(1));
    // we need at least one token
    if tok.is_empty() {
        Err(Err::Incomplete(Needed::new(1)))
    } else {
        let id = tok.peek();
        match &id.content {
            TokenContent::IntLiteral(s) => Ok((rem, *s)),
            _ => Err(Err::Error(VrsError::from_token(
                input,
                TokenContent::IntLiteral(0),
            ))),
        }
    }
}

pub fn boolean(input: TokenStream) -> IResult<TokenStream, bool> {
    let (rem, tok) = try_parse!(input.clone(), take!(1));
    // we need at least one token
    if tok.is_empty() {
        Err(Err::Incomplete(Needed::new(1)))
    } else {
        let id = tok.peek();
        match &id.content {
            TokenContent::BoolLiteral(s) => Ok((rem, *s)),
            _ => Err(Err::Error(VrsError::from_token(
                input,
                TokenContent::BoolLiteral(false),
            ))),
        }
    }
}

macro_rules! keywordparser (
    ($vis:vis $name:ident, $tag: expr) => (
        $vis fn $name(input: TokenStream) -> IResult<TokenStream, ()> {
            let (rem, tok) = try_parse!(input.clone(), take!(1));
            // we need at least one token
            if tok.is_empty() {
                Err(Err::Incomplete(Needed::new(1)))
            } else {
                if tok.peek().content == TokenContent::Keyword($tag) {
                    Ok((rem, ()))
                } else {
                    Err(Err::Error(VrsError::from_token(input, TokenContent::Keyword($tag))))
                }
            }
        }
    )
);

keywordparser!(pub kw_unit, Keyword::Unit);
keywordparser!(pub kw_import, Keyword::Import);
keywordparser!(pub kw_const, Keyword::Const);
keywordparser!(pub kw_let, Keyword::Let);
keywordparser!(pub kw_if, Keyword::If);
keywordparser!(pub kw_else, Keyword::Else);

/// parses a type expression
///
/// returns the type
pub fn typeinfo(input: TokenStream) -> IResult<TokenStream, Type> {
    // we start with the or expression (|)
    let (rem, tok) = try_parse!(input.clone(), take!(1));
    if tok.is_empty() {
        return Err(Err::Incomplete(Needed::new(1)));
    }

    match tok.peek().content {
        TokenContent::Keyword(Keyword::Size) => Ok((rem, Type::Size)),
        TokenContent::Keyword(Keyword::Addr) => Ok((rem, Type::Address)),
        TokenContent::Keyword(Keyword::Boolean) => Ok((rem, Type::Boolean)),
        TokenContent::Keyword(Keyword::Integer) => Ok((rem, Type::Integer)),
        // TODO: make this more type specifc
        _ => Err(Err::Error(VrsError::from_token(
            input,
            TokenContent::Keyword(Keyword::Size),
        ))),
    }
}
