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
use nom::{bytes::complete::take, Err, Needed};

// library internal includes
use crate::ast::Type;
use crate::error::{IResult, VrsError};
use crate::token::{Keyword, TokenContent, TokenStream};

/// ff
macro_rules! terminalparser (
    ($vis:vis $name:ident, $tag: expr) => (
        $vis fn $name(input: TokenStream) -> IResult<TokenStream, TokenContent> {
            let (rem, tok) = take(1usize)(input.clone())?;
            // we need at least one token
            if tok.is_empty() {
                Err(Err::Incomplete(Needed::new(1)))
            } else {
                if tok.peek().content == $tag {
                    Ok((rem, $tag))
                } else {
                    Err(Err::Error(VrsError::from_token(input.with_range(0..1), $tag)))
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
terminalparser!(pub larrow, TokenContent::LArrow);
terminalparser!(pub rarrow, TokenContent::RArrow);
terminalparser!(pub bidirarrow, TokenContent::BiDirArrow);
terminalparser!(pub fatarrow, TokenContent::FatArrow);
terminalparser!(pub bidirfatarrow, TokenContent::BiDirFatArrow);
terminalparser!(pub rlongfatarrow, TokenContent::RLongFatArrow);

// comparators
terminalparser!(pub at, TokenContent::At);
terminalparser!(pub dotdot, TokenContent::DotDot);
terminalparser!(pub pathsep, TokenContent::PathSep);
terminalparser!(pub wildcard, TokenContent::Wildcard);
terminalparser!(pub eof, TokenContent::Eof);

pub fn ident(input: TokenStream) -> IResult<TokenStream, String> {
    let (rem, tok) = take(1usize)(input.clone())?;
    // we need at least one token
    if tok.is_empty() {
        Err(Err::Incomplete(Needed::new(1)))
    } else {
        let id = tok.peek();
        match &id.content {
            TokenContent::Identifier(s) => Ok((rem, s.clone())),
            _ => Err(Err::Error(VrsError::from_token(
                input.with_range(0..1),
                TokenContent::Identifier(String::new()),
            ))),
        }
    }
}

pub fn num(input: TokenStream) -> IResult<TokenStream, u64> {
    let (rem, tok) = take(1usize)(input.clone())?;
    // we need at least one token
    if tok.is_empty() {
        Err(Err::Incomplete(Needed::new(1)))
    } else {
        let id = tok.peek();
        match &id.content {
            TokenContent::IntLiteral(s) => Ok((rem, *s)),
            _ => Err(Err::Error(VrsError::from_token(
                input.with_range(0..1),
                TokenContent::IntLiteral(0),
            ))),
        }
    }
}

pub fn boolean(input: TokenStream) -> IResult<TokenStream, bool> {
    let (rem, tok) = take(1usize)(input.clone())?;
    // we need at least one token
    if tok.is_empty() {
        Err(Err::Incomplete(Needed::new(1)))
    } else {
        let id = tok.peek();
        match &id.content {
            TokenContent::BoolLiteral(s) => Ok((rem, *s)),
            _ => Err(Err::Error(VrsError::from_token(
                input.with_range(0..1),
                TokenContent::BoolLiteral(false),
            ))),
        }
    }
}

macro_rules! keywordparser (
    ($vis:vis $name:ident, $tag: expr) => (
        $vis fn $name(input: TokenStream) -> IResult<TokenStream, Keyword> {
            let (rem, tok) = take(1usize)(input.clone())?;
            // we need at least one token
            if tok.is_empty() {
                Err(Err::Incomplete(Needed::new(1)))
            } else {
                if tok.peek().content == TokenContent::Keyword($tag) {
                    Ok((rem, $tag))
                } else {
                    Err(Err::Error(VrsError::from_token(input.with_range(0..1), TokenContent::Keyword($tag))))
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
keywordparser!(pub kw_state, Keyword::State);
keywordparser!(pub kw_interface, Keyword::Interface);
keywordparser!(pub kw_memorystate, Keyword::MemoryState);
keywordparser!(pub kw_registerstate, Keyword::RegisterState);
keywordparser!(pub kw_memoryinterface, Keyword::MemoryInterface);
keywordparser!(pub kw_mmiointerface, Keyword::MMIOInterface);
keywordparser!(pub kw_cpuregisterinterface, Keyword::CPURegisterInterface);
keywordparser!(pub kw_none, Keyword::None);
keywordparser!(pub kw_layout, Keyword::Layout);
keywordparser!(pub kw_fn, Keyword::Fn);
keywordparser!(pub kw_size, Keyword::SizeType);
keywordparser!(pub kw_readaction, Keyword::ReadAction);
keywordparser!(pub kw_writeaction, Keyword::WriteAction);
keywordparser!(pub kw_requires, Keyword::Requires);
keywordparser!(pub kw_ensures, Keyword::Ensures);
keywordparser!(pub kw_assert, Keyword::Assert);
keywordparser!(pub kw_return, Keyword::Return);
keywordparser!(pub kw_forall, Keyword::Forall);
keywordparser!(pub kw_exists, Keyword::Exists);
keywordparser!(pub kw_staticmap, Keyword::StaticMap);
keywordparser!(pub kw_segment, Keyword::Segment);
keywordparser!(pub kw_for, Keyword::For);
keywordparser!(pub kw_in, Keyword::In);
keywordparser!(pub kw_inbitwidth, Keyword::InBitWidth);
keywordparser!(pub kw_outbitwidth, Keyword::OutBitWidth);
keywordparser!(pub kw_flags, Keyword::FlagsType);

/// parses a type expression
///
/// returns the type
pub fn typeinfo(input: TokenStream) -> IResult<TokenStream, Type> {
    // we start with the or expression (|)
    let (rem, tok) = take(1usize)(input.clone())?;
    if tok.is_empty() {
        return Err(Err::Incomplete(Needed::new(1)));
    }

    match tok.peek().content {
        TokenContent::Keyword(Keyword::SizeType) => Ok((rem, Type::Size)),
        TokenContent::Keyword(Keyword::AddrType) => Ok((rem, Type::Address)),
        TokenContent::Keyword(Keyword::BooleanType) => Ok((rem, Type::Boolean)),
        TokenContent::Keyword(Keyword::IntegerType) => Ok((rem, Type::Integer)),
        TokenContent::Keyword(Keyword::FlagsType) => Ok((rem, Type::Flags)),
        // TODO: make this more type specifc
        _ => Err(Err::Error(VrsError::from_token(
            input.with_range(0..1),
            TokenContent::Keyword(Keyword::SizeType),
        ))),
    }
}
