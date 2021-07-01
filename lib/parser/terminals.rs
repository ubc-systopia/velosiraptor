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

// get the lexer tokens
use crate::lexer::token::{TokenContent, TokenStream};

// NOM parsing constructs
use nom::{take, try_parse};
// NOM results
use nom::{error_position, Err, IResult, Needed};
// NOM error kind
use nom::error::ErrorKind;

macro_rules! namedtag (
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
                    Err(Err::Error(error_position!(input, ErrorKind::Tag)))
                }
            }
        }
    )
);

// keywords
namedtag!(pub import_keyword, TokenContent::Import);
namedtag!(pub unit_keyword, TokenContent::Unit);

// punctuation
namedtag!(pub comma, TokenContent::Comma);
namedtag!(pub colon, TokenContent::Colon);
namedtag!(pub semicolon, TokenContent::SemiColon);

// parenthesis
namedtag!(pub lparen, TokenContent::LParen);
namedtag!(pub rparen, TokenContent::RParen);
namedtag!(pub lbrace, TokenContent::LBrace);
namedtag!(pub rbrace, TokenContent::RBrace);
namedtag!(pub lbrack, TokenContent::LBracket);
namedtag!(pub rbrack, TokenContent::RBracket);

// operators
namedtag!(pub plus, TokenContent::Plus);
namedtag!(pub minus, TokenContent::Minus);
namedtag!(pub multiply, TokenContent::Multiply);
namedtag!(pub lshift, TokenContent::LShift);
namedtag!(pub rshift, TokenContent::RShift);
namedtag!(pub equal, TokenContent::Equal);

pub fn ident(input: TokenStream) -> IResult<TokenStream, String> {
    let (rem, tok) = try_parse!(input.clone(), take!(1));
    // we need at least one token
    if tok.is_empty() {
        Err(Err::Incomplete(Needed::new(1)))
    } else {
        let id = tok.peek();
        match &id.content {
            TokenContent::Identifier(s) => Ok((rem, s.clone())),
            _ => Err(Err::Error(error_position!(input, ErrorKind::AlphaNumeric))),
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
            _ => Err(Err::Error(error_position!(input, ErrorKind::Digit))),
        }
    }
}
