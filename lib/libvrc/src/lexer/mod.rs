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

//! Lexer Module of the Velosiraptor Compiler

use custom_error::custom_error;
use std::fs;
use std::rc::Rc;

mod comments;
mod identifier;
mod number;
pub mod sourcepos;
pub mod token;

use self::comments::*;
use self::identifier::identifier;
use self::number::number;
use self::sourcepos::SourcePos;
use self::token::*;

// custom error definitions
custom_error! { #[derive(PartialEq)] pub LexerError
  ReadSourceFile{ file: String } = "Could not read the source file",
  NoTokens                       = "No tokens found. Need to lex first"
}

/// represents the lexer state
pub struct Lexer;

use nom::{
    alt, branch::alt, bytes::complete::tag, character::complete::multispace0, multi::many1, named,
    sequence::delimited, IResult,
};

macro_rules! namedtag (
    ($vis:vis $name:ident, $tag: expr) => (
        $vis fn $name(input: SourcePos) -> IResult<SourcePos, Token> {
            match tag(TokenContent::to_str($tag))(input) {
                Ok((i, s)) => Ok((i, Token::new($tag, s))),
                Err(x) => Err(x)
            }
        }
    )
);

// delimiters
namedtag!(lparen, TokenContent::LParen);
namedtag!(rparen, TokenContent::RParen);
namedtag!(lbrace, TokenContent::LBrace);
namedtag!(rbrace, TokenContent::RBrace);
namedtag!(lbrack, TokenContent::LBracket);
namedtag!(rbrack, TokenContent::RBracket);

// punctuations
namedtag!(dot, TokenContent::Dot);
namedtag!(comma, TokenContent::Comma);
namedtag!(colon, TokenContent::Colon);
namedtag!(semicolon, TokenContent::SemiColon);

// operators
namedtag!(plus, TokenContent::Plus);
namedtag!(minus, TokenContent::Minus);
namedtag!(star, TokenContent::Star);
namedtag!(slash, TokenContent::Slash);
namedtag!(percent, TokenContent::Percent);

// shifts
namedtag!(lshift, TokenContent::LShift);
namedtag!(rshift, TokenContent::RShift);

// bitwise operators
namedtag!(not, TokenContent::Not);
namedtag!(and, TokenContent::And);
namedtag!(or, TokenContent::Or);
namedtag!(xor, TokenContent::Xor);

// logical operators
namedtag!(lnot, TokenContent::LNot);
namedtag!(land, TokenContent::LAnd);
namedtag!(lor, TokenContent::LOr);

// comparators
namedtag!(eq, TokenContent::Eq);
namedtag!(ne, TokenContent::Ne);
namedtag!(le, TokenContent::Le);
namedtag!(ge, TokenContent::Ge);
namedtag!(lt, TokenContent::Lt);
namedtag!(gt, TokenContent::Gt);

// assignment
namedtag!(assign, TokenContent::Assign);

// arrows
namedtag!(fatarrow, TokenContent::FatArrow);
namedtag!(rarrow, TokenContent::RArrow);

// comparators
namedtag!(at, TokenContent::At);
namedtag!(underscore, TokenContent::Underscore);
namedtag!(dotdot, TokenContent::DotDot);
namedtag!(pathsep, TokenContent::PathSep);
namedtag!(wildcard, TokenContent::Wildcard);

named!(punctuation<SourcePos, Token>, alt!(
    // two symbols that make up this token
    dotdot | pathsep | lshift | rshift | rarrow | fatarrow |
    lnot | land | lor | eq | ne | le | ge |

    // single symbol tokens
    xor | not | and | or | lt | gt |
    assign | at | underscore | wildcard |
    plus | minus | star | slash | percent |
    lparen | rparen | rbrace | lbrace | lbrack | rbrack |
    dot | comma | colon | semicolon
));

fn tokens(input: SourcePos) -> IResult<SourcePos, Token> {
    delimited(
        multispace0,
        alt((identifier, number, blockcomment, linecomment, punctuation)),
        multispace0,
    )(input)
}

impl Lexer {
    /// Constructs a vector of Tokens corresponding to Lexemes for the SourcePos
    ///
    /// During the lexing process, all whitespace wil be dropped. Comments remain
    /// as Tokens.
    pub fn lex_source_pos(sp: SourcePos) -> Result<Vec<Token>, LexerError> {
        log::debug!("start lexing...");
        let (i, tok) = match many1(tokens)(sp) {
            Ok((r, tok)) => (r, tok),
            Err(x) => return Err(LexerError::NoTokens),
        };
        log::debug!("lexing done.");
        Ok(tok)
    }

    /// Performs lexing on a supplied string and context.
    ///
    /// This function will create a new `SourcePos` for the supplied string, and
    /// hence create a copy of the supplied string.
    pub fn lex_string(context: &str, string: &str) -> Result<Vec<Token>, LexerError> {
        log::info!("lexing stirng wtih context '{}'", context);
        let sp = SourcePos::new(context, string);
        Lexer::lex_source_pos(sp)
    }

    /// Performs lexing on a file given by the filename.
    ///
    /// Opens and reads the file contents, and lexes it. Besides a vector of tokens,
    /// it also returns a reference-counded String of the file contents.
    pub fn lex_file(filename: &str) -> Result<(Vec<Token>, Rc<String>), LexerError> {
        log::info!("creating file parser for '{}'", filename);

        // read the file
        let file_contents = fs::read_to_string(&filename);

        // create a new reference counted String object
        let contents = match file_contents {
            Ok(s) => Rc::new(s),
            _ => {
                log::error!("could not read the file '{}'", filename);
                return Err(LexerError::ReadSourceFile {
                    file: filename.to_string(),
                });
            }
        };

        // Create the new source position
        let sp = SourcePos::from_string(Rc::new(filename.to_string()), contents.clone());

        // lex it and return the result along with the file contents
        match Lexer::lex_source_pos(sp) {
            Ok(toks) => Ok((toks, contents)),
            Err(x) => Err(x),
        }
    }
}

#[cfg(test)]
use std::path::PathBuf;

#[cfg(test)]
use nom::Slice;

/// Operator lexing tests
#[test]
fn operator_tests() {
    let contents = "+++";
    let sp = SourcePos::new("stdio", contents);
    assert_eq!(
        Lexer::lex_string("stdio", contents),
        Lexer::lex_source_pos(sp.clone())
    );
    assert_eq!(
        Lexer::lex_source_pos(sp.clone()),
        Ok(vec![
            Token::new(TokenContent::Plus, sp.slice(0..1)),
            Token::new(TokenContent::Plus, sp.slice(1..2)),
            Token::new(TokenContent::Plus, sp.slice(2..3)),
        ])
    );

    let contents = "==+<<>";
    let sp = SourcePos::new("stdio", contents);
    assert_eq!(
        Lexer::lex_source_pos(sp.clone()),
        Ok(vec![
            Token::new(TokenContent::Eq, sp.slice(0..2)),
            Token::new(TokenContent::Plus, sp.slice(2..3)),
            Token::new(TokenContent::LShift, sp.slice(3..5)),
            Token::new(TokenContent::Gt, sp.slice(5..6)),
        ])
    );
}

/// test lexing of files
#[test]
fn empty_file_tests() {
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("tests/lexer");

    for f in vec!["emptyfile.vrs", "whitespace.vrs"] {
        d.push(f);
        let filename = format!("{}", d.display());

        // lex the file
        let err = Lexer::lex_file(&filename);
        assert!(err.is_err());

        d.pop();
    }

    for f in vec!["comments.vrs"] {
        d.push(f);
        let filename = format!("{}", d.display());

        // lex the file
        let err = Lexer::lex_file(&filename);
        assert!(err.is_ok());

        d.pop();
    }
}

/// test lexing of files
#[test]
fn basic_tests() {
    let content = "import foobar; /* comment */unit abc {}; // end of file";
    let tok = match Lexer::lex_string("stdio", content) {
        Ok(vec) => vec,
        Err(_) => panic!("lexing failed"),
    };
    // there should be 10 tokens
    assert_eq!(tok.len(), 10);
}
