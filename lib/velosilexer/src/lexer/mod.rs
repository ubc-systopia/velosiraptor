// Velosilexer -- Lexer Module
//
//
// MIT License
//
// Copyright (c) 2021, 2022 Systopia Lab, Computer Science, University of British Columbia
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

// used exernal dependencies
use nom::{
    branch::alt,
    bytes::complete::{tag, take},
    character::complete::multispace0,
    combinator::all_consuming,
    multi::many0,
    sequence::delimited,
    Err,
};

use crate::error::{IResult, VelosiLexerErrBuilder};
use crate::{SrcSpan, Tok, VelosiOpToken, VelosiToken, VelosiTokenKind};

mod comments;
mod identifier;
mod number;

use comments::{blockcomment, linecomment};
use identifier::identifier;
use number::number;

// macro to generate a parser to recognize a token
macro_rules! namedtag (
    ($vis:vis $name:ident, $tag: expr) => (
        $vis fn $name(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
            let (i, s) = tag($tag.as_str())(input)?;
            Ok((i, Tok::new(VelosiTokenKind::OpToken($tag), s)))
        }
    )
);

// // delimiters
namedtag!(lparen, VelosiOpToken::LParen);
namedtag!(rparen, VelosiOpToken::RParen);
namedtag!(lbrace, VelosiOpToken::LBrace);
namedtag!(rbrace, VelosiOpToken::RBrace);
namedtag!(lbrack, VelosiOpToken::LBracket);
namedtag!(rbrack, VelosiOpToken::RBracket);

// punctuations
namedtag!(dot, VelosiOpToken::Dot);
namedtag!(comma, VelosiOpToken::Comma);
namedtag!(colon, VelosiOpToken::Colon);
namedtag!(semicolon, VelosiOpToken::SemiColon);

// operators
namedtag!(plus, VelosiOpToken::Plus);
namedtag!(minus, VelosiOpToken::Minus);
namedtag!(star, VelosiOpToken::Star);
namedtag!(slash, VelosiOpToken::Slash);
namedtag!(percent, VelosiOpToken::Percent);

// shifts
namedtag!(lshift, VelosiOpToken::LShift);
namedtag!(rshift, VelosiOpToken::RShift);

// bitwise operators
namedtag!(not, VelosiOpToken::Not);
namedtag!(and, VelosiOpToken::And);
namedtag!(or, VelosiOpToken::Or);
namedtag!(xor, VelosiOpToken::Xor);

// logical operators
namedtag!(lnot, VelosiOpToken::LNot);
namedtag!(land, VelosiOpToken::LAnd);
namedtag!(lor, VelosiOpToken::LOr);

// comparators
namedtag!(eq, VelosiOpToken::Eq);
namedtag!(ne, VelosiOpToken::Ne);
namedtag!(le, VelosiOpToken::Le);
namedtag!(ge, VelosiOpToken::Ge);
namedtag!(lt, VelosiOpToken::Lt);
namedtag!(gt, VelosiOpToken::Gt);

// assignment
namedtag!(assign, VelosiOpToken::Assign);

// arrows
namedtag!(larrow, VelosiOpToken::LArrow);
namedtag!(rarrow, VelosiOpToken::RArrow);
namedtag!(bidirarrow, VelosiOpToken::BiDirArrow);
namedtag!(fatarrow, VelosiOpToken::FatArrow);
namedtag!(bidirfatarrow, VelosiOpToken::BiDirFatArrow);
namedtag!(rlongfatarrow, VelosiOpToken::RLongFatArrow);

// misc
namedtag!(at, VelosiOpToken::At);
namedtag!(dotdot, VelosiOpToken::DotDot);
namedtag!(coloncolon, VelosiOpToken::ColonColon);
namedtag!(questionmark, VelosiOpToken::QuestionMark);
namedtag!(hashtag, VelosiOpToken::HashTag);

/// symbols with two character width
fn punctuation2(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
    alt((
        // arrows etc
        rlongfatarrow,
        dotdot,
        coloncolon,
        larrow,
        rarrow,
        bidirarrow,
        fatarrow,
        bidirfatarrow, // shifts
        fatarrow,      // shifts
        lshift,
        rshift, // logical combinations
        land,
        lor, // comparisons
        eq,
        ne,
        le,
        ge,
    ))(input)
}

/// parser for different parenthesis
fn parens(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
    alt((lparen, rparen, rbrace, lbrace, lbrack, rbrack))(input)
}

/// parser for arithmetic operations
fn arithop(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
    alt((plus, minus, star, slash, percent))(input)
}

/// parser for bitwise operators
fn bitwiseop(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
    alt((xor, not, and, or))(input)
}

fn puncts(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
    alt((dot, comma, colon, semicolon))(input)
}

/// sybols with one caracter with
fn punctuation1(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
    alt((
        arithop,
        lnot,
        bitwiseop,
        lt,
        gt,
        parens,
        puncts,
        assign,
        questionmark,
        at,
        hashtag,
    ))(input)
}

fn any(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
    let (_, t) = take(1usize)(input)?;

    let errmsg = format!("Not supported character encountered: `{}`", t.as_str());
    let err = VelosiLexerErrBuilder::new(errmsg)
        .add_hint("Remove this unsupported character".to_string())
        .add_location(t)
        .build();
    Err(Err::Failure(err))
}

/// recognizes a token
fn token(input: SrcSpan) -> IResult<SrcSpan, VelosiToken> {
    delimited(
        multispace0,
        alt((
            identifier,
            number,
            blockcomment,
            linecomment,
            punctuation2,
            punctuation1,
            any,
        )),
        multispace0,
    )(input)
}

/// lexes a source span into a list of tokens
pub fn lex(input: SrcSpan) -> IResult<SrcSpan, Vec<VelosiToken>> {
    // if it's an empty file, simply return the empty token list
    if input.is_empty() {
        return Ok((input, Vec::new()));
    }

    // // try to consume all leading spaces. If we obtain the same length back, then
    // // this indicates that we don't have any actual content in the input
    let (input, _) = multispace0(input)?;
    if input.is_empty() {
        return Ok((input, Vec::new()));
    }

    // finally see whether we can lex the entire input
    all_consuming(many0(token))(input)
}
