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

// NOM parsing constructs
use nom::{branch::alt, bytes::complete::take, combinator::map, Err, Needed};

// library internal includes
use crate::error::{IResult, VelosiParserErr};
use crate::parsetree::{VelosiParseTreeType, VelosiParseTreeTypeInfo};
use crate::{VelosiKeyword, VelosiOpToken, VelosiTokenKind, VelosiTokenStream};

// ff
macro_rules! terminalparser (($vis:vis $name:ident, $tag: expr) => (
    $vis fn $name(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiTokenKind> {
        // we hit EOF, report the expected string
        if input.len() == 0 {
            let expected = VelosiTokenKind::OpToken($tag);
            return Err(Err::Error(VelosiParserErr::from_expected(input, expected)));
        }

        let (rem, tok) = take(1usize)(input.clone())?;
        // unwrap the token and check it if it matches
        let t = tok.peek().unwrap();
        if *t.kind() == VelosiTokenKind::OpToken($tag) {
            Ok((rem, VelosiTokenKind::OpToken($tag)))
        } else {
            let expected = VelosiTokenKind::OpToken($tag);
            Err(Err::Error(VelosiParserErr::from_expected(input.from_self_with_subrange(0..1), expected)))
        }
    }
));

// delimiters
terminalparser!(pub lparen, VelosiOpToken::LParen);
terminalparser!(pub rparen, VelosiOpToken::RParen);
terminalparser!(pub lbrace, VelosiOpToken::LBrace);
terminalparser!(pub rbrace, VelosiOpToken::RBrace);
terminalparser!(pub lbrack, VelosiOpToken::LBracket);
terminalparser!(pub rbrack, VelosiOpToken::RBracket);

// punctuations
terminalparser!(pub dot, VelosiOpToken::Dot);
terminalparser!(pub comma, VelosiOpToken::Comma);
terminalparser!(pub colon, VelosiOpToken::Colon);
terminalparser!(pub semicolon, VelosiOpToken::SemiColon);

// operators
terminalparser!(pub plus, VelosiOpToken::Plus);
terminalparser!(pub minus, VelosiOpToken::Minus);
terminalparser!(pub star, VelosiOpToken::Star);
terminalparser!(pub slash, VelosiOpToken::Slash);
terminalparser!(pub percent, VelosiOpToken::Percent);

// shifts
terminalparser!(pub lshift, VelosiOpToken::LShift);
terminalparser!(pub rshift, VelosiOpToken::RShift);

// bitwise operators
terminalparser!(pub not, VelosiOpToken::Not);
terminalparser!(pub and, VelosiOpToken::And);
terminalparser!(pub or, VelosiOpToken::Or);
terminalparser!(pub xor, VelosiOpToken::Xor);

// logical operators
terminalparser!(pub lnot, VelosiOpToken::LNot);
terminalparser!(pub land, VelosiOpToken::LAnd);
terminalparser!(pub lor, VelosiOpToken::LOr);

// comparators
terminalparser!(pub eq, VelosiOpToken::Eq);
terminalparser!(pub ne, VelosiOpToken::Ne);
terminalparser!(pub le, VelosiOpToken::Le);
terminalparser!(pub ge, VelosiOpToken::Ge);
terminalparser!(pub lt, VelosiOpToken::Lt);
terminalparser!(pub gt, VelosiOpToken::Gt);

// assignment
terminalparser!(pub assign, VelosiOpToken::Assign);

// arrows
terminalparser!(pub larrow, VelosiOpToken::LArrow);
terminalparser!(pub rarrow, VelosiOpToken::RArrow);
terminalparser!(pub bidirarrow, VelosiOpToken::BiDirArrow);
terminalparser!(pub fatarrow, VelosiOpToken::FatArrow);
terminalparser!(pub bidirfatarrow, VelosiOpToken::BiDirFatArrow);
terminalparser!(pub rlongfatarrow, VelosiOpToken::RLongFatArrow);

// comparators
// terminalparser!(pub at, VelosiOpToken::At);
terminalparser!(pub dotdot, VelosiOpToken::DotDot);
terminalparser!(pub coloncolon, VelosiOpToken::ColonColon);
// terminalparser!(pub questionmark, VelosiOpToken::QuestionMark);

pub fn ident(mut input: VelosiTokenStream) -> IResult<VelosiTokenStream, String> {
    // we hit EOF, report the expected string
    if input.len() == 0 {
        let expected = VelosiTokenKind::Identifier(String::new());
        return Err(Err::Error(VelosiParserErr::from_expected(input, expected)));
    }

    // now we can take the first token
    let (rem, tok) = take(1usize)(input.clone())?;

    // unwrap the token and check it if it matches
    let t = tok.peek().unwrap();
    if let VelosiTokenKind::Identifier(s) = t.kind() {
        Ok((rem, s.clone()))
    } else {
        let expected = VelosiTokenKind::Identifier(String::new());
        let err = VelosiParserErr::from_expected(input.from_self_with_subrange(0..1), expected);
        Err(Err::Error(err))
    }
}

pub fn num(input: VelosiTokenStream) -> IResult<VelosiTokenStream, u64> {
    // we hit EOF, report the expected number
    if input.len() == 0 {
        let expected = VelosiTokenKind::NumLiteral(0);
        return Err(Err::Error(VelosiParserErr::from_expected(input, expected)));
    }

    let (rem, tok) = take(1usize)(input.clone())?;

    // unwrap the token and check it if it matches
    let t = tok.peek().unwrap();
    if let VelosiTokenKind::NumLiteral(s) = t.kind() {
        Ok((rem, *s))
    } else {
        let expected = VelosiTokenKind::NumLiteral(0);
        let err = VelosiParserErr::from_expected(input.from_self_with_subrange(0..1), expected);
        Err(Err::Error(err))
    }
}

pub fn boolean(input: VelosiTokenStream) -> IResult<VelosiTokenStream, bool> {
    // we hit EOF, report the expected boolean
    if input.len() == 0 {
        let expected = VelosiTokenKind::BoolLiteral(false);
        return Err(Err::Error(VelosiParserErr::from_expected(input, expected)));
    }

    let (rem, tok) = take(1usize)(input.clone())?;

    // unwrap the token and check it if it matches
    let t = tok.peek().unwrap();
    if let VelosiTokenKind::BoolLiteral(s) = t.kind() {
        Ok((rem, *s))
    } else {
        let expected = VelosiTokenKind::BoolLiteral(false);
        let err = VelosiParserErr::from_expected(input.from_self_with_subrange(0..1), expected);
        Err(Err::Error(err))
    }
}

macro_rules! keywordparser (($vis:vis $name:ident, $tag: expr) => (
    $vis fn $name(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiKeyword> {
        // we hit EOF, report the expected number
        if input.len() == 0 {
            let expected = VelosiTokenKind::Keyword($tag);
            return Err(Err::Error(VelosiParserErr::from_expected(input, expected)));
        }

        let (rem, tok) = take(1usize)(input.clone())?;

        // unwrap the token and check it if it matches
        let t = tok.peek().unwrap();
        if *t.kind() == VelosiTokenKind::Keyword($tag) {
            Ok((rem, $tag))
        } else {
            let expected = VelosiTokenKind::Keyword($tag);
            let err = VelosiParserErr::from_expected(input.from_self_with_subrange(0..1), expected);
            Err(Err::Error(err))
        }
    }
));

keywordparser!(pub kw_unit, VelosiKeyword::Unit);
keywordparser!(pub kw_import, VelosiKeyword::Import);
keywordparser!(pub kw_const, VelosiKeyword::Const);
// keywordparser!(pub kw_let, VelosiKeyword::Let);
keywordparser!(pub kw_if, VelosiKeyword::If);
keywordparser!(pub kw_else, VelosiKeyword::Else);
// keywordparser!(pub kw_state, VelosiKeyword::State);
// keywordparser!(pub kw_interface, VelosiKeyword::Interface);
// keywordparser!(pub kw_memorystate, VelosiKeyword::MemoryState);
// keywordparser!(pub kw_registerstate, VelosiKeyword::RegisterState);
// keywordparser!(pub kw_memoryinterface, VelosiKeyword::MemoryInterface);
// keywordparser!(pub kw_mmiointerface, VelosiKeyword::MMIOInterface);
// keywordparser!(pub kw_cpuregisterinterface, VelosiKeyword::CPURegisterInterface);
// keywordparser!(pub kw_none, VelosiKeyword::None);
// keywordparser!(pub kw_layout, VelosiKeyword::Layout);
// keywordparser!(pub kw_fn, VelosiKeyword::Fn);
// keywordparser!(pub kw_readaction, VelosiKeyword::ReadAction);
// keywordparser!(pub kw_writeaction, VelosiKeyword::WriteAction);
// keywordparser!(pub kw_requires, VelosiKeyword::Requires);
// keywordparser!(pub kw_ensures, VelosiKeyword::Ensures);
// keywordparser!(pub kw_assert, VelosiKeyword::Assert);
// keywordparser!(pub kw_return, VelosiKeyword::Return);
keywordparser!(pub kw_forall, VelosiKeyword::Forall);
keywordparser!(pub kw_exists, VelosiKeyword::Exists);
keywordparser!(pub kw_staticmap, VelosiKeyword::StaticMap);
keywordparser!(pub kw_segment, VelosiKeyword::Segment);
// keywordparser!(pub kw_for, VelosiKeyword::For);
// keywordparser!(pub kw_in, VelosiKeyword::In);
keywordparser!(pub kw_inbitwidth, VelosiKeyword::InBitWidth);
keywordparser!(pub kw_outbitwidth, VelosiKeyword::OutBitWidth);
// keywordparser!(pub kw_flags, VelosiKeyword::FlagsType);

// types
keywordparser!(pub kw_size, VelosiKeyword::SizeType);
keywordparser!(pub kw_flags, VelosiKeyword::FlagsType);
keywordparser!(pub kw_addr, VelosiKeyword::AddressType);
keywordparser!(pub kw_vaddr, VelosiKeyword::VAddrType);
keywordparser!(pub kw_paddr, VelosiKeyword::PAddrType);
keywordparser!(pub kw_bool, VelosiKeyword::BooleanType);
keywordparser!(pub kw_int, VelosiKeyword::IntegerType);

fn builtin_type(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeTypeInfo> {
    let mut pos = input.clone();
    let (rem, tok) = alt((
        kw_size, kw_flags, kw_addr, kw_vaddr, kw_paddr, kw_bool, kw_int,
    ))(input)?;

    let ti = match tok {
        VelosiKeyword::SizeType => VelosiParseTreeTypeInfo::Size,
        VelosiKeyword::FlagsType => VelosiParseTreeTypeInfo::Flags,
        VelosiKeyword::AddressType => VelosiParseTreeTypeInfo::GenAddr,
        VelosiKeyword::VAddrType => VelosiParseTreeTypeInfo::VirtAddr,
        VelosiKeyword::PAddrType => VelosiParseTreeTypeInfo::PhysAddr,
        VelosiKeyword::BooleanType => VelosiParseTreeTypeInfo::Bool,
        VelosiKeyword::IntegerType => VelosiParseTreeTypeInfo::Integer,
        _ => unreachable!(),
    };
    Ok((rem, ti))
}

/// parses a type expression
///
/// returns the type
pub fn typeinfo(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeType> {
    let mut pos = input.clone();
    let (rem, tok) = alt((
        builtin_type,
        map(ident, |x| VelosiParseTreeTypeInfo::TypeRef(x)),
    ))(input)?;

    pos.span_until_start(&rem);
    Ok((rem, VelosiParseTreeType::new(tok, pos)))
}
