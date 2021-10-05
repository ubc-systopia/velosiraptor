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

//! Velosiraptor Lexer Tokens

use nom::InputLength;
use std::fmt;

use crate::sourcepos::SourcePos;

/// Represents the keywords we have
#[derive(PartialEq, Debug, Clone)]
pub enum Keyword {
    /// constant values
    Const,
    /// unit definitins
    Unit,
    /// conditional statemt
    If,
    /// conditional else branch
    Else,
    /// import statements
    Import,
    /// state statement
    State,
    /// interface statement
    Interface,
    /// Memory State and Interface statement
    Memory,
    /// Memory Mapped Interface statement
    MMIO,
    /// Register State and Interface statement
    Register,
    /// Null-like value used for State and Interface
    None,
    /// Action types used in Interface
    ReadAction,
    WriteAction,
    /// Used in identifying the Bitslice layout of an Interface field
    Layout,
    /// defines a local variable
    Let,
    /// represents a function
    Fn,
    /// An assert statement
    Assert,
    /// represents an address value
    Addr,
    /// represents a size value
    Size,
    /// A boolean type
    Boolean,
    /// An integer value
    Integer,
    /// the requires clause
    Requires,
    /// the ensures clause
    Ensures,
    /// the return keyword
    Return,
}

/// Implementation of the [std::fmt::Display] trait for [Token]
impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Keyword::*;
        let kwstr = match self {
            Const => "const",
            Unit => "unit",
            If => "if",
            Else => "else",
            Import => "import",
            Let => "let",
            Fn => "fn",
            Assert => "assert",
            State => "state",
            Interface => "Interface",
            Memory => "Memory",
            MMIO => "MMIO",
            Register => "Register",
            None => "None",
            Requires => "requires",
            Ensures => "ensures",
            Return => "return",
            Layout => "Layout",
            // ActionTypes
            ReadAction => "ReadAction",
            WriteAction => "WriteAction",
            // types
            Addr => "addr",
            Size => "size",
            Boolean => "bool",
            Integer => "int",
        };
        write!(f, "{}", kwstr)
    }
}

/// Represents the content of a token
#[derive(PartialEq, Clone)]
pub enum TokenContent {
    // end of file
    Eof,

    // illegal token
    Illegal,

    // literals, integers of booleans
    IntLiteral(u64),   // 1234 0x134 0o1234 0b1111
    BoolLiteral(bool), // true | false

    // identifier
    Identifier(String), // abc ab_cd

    // Keywords
    Keyword(Keyword), // unit | import

    // comments
    Comment(String),      // //
    BlockComment(String), // /* */

    // punctuations
    Dot,       // .
    Comma,     // ,
    Colon,     // :
    SemiColon, // ;

    // delimiters
    LParen,   // (
    RParen,   // )
    LBrace,   // {
    RBrace,   // }
    LBracket, // [
    RBracket, // ]

    // operators
    Plus,    // +
    Minus,   // -
    Star,    // *
    Slash,   // /
    Percent, // %  (remainder)
    LShift,  // <<
    RShift,  // >>

    // bitwise operators
    Xor, // ^  (xor)
    Not, // ~
    And, // &
    Or,  // |

    // logical operators
    LNot, // ! logical not
    LAnd, // &&
    LOr,  // ||

    // assignments
    Assign, // =

    // arrows
    LArrow,        // <-
    RArrow,        // ->
    BiDirArrow,    // <->
    FatArrow,      // =>
    BiDirFatArrow, // <=>

    // comparisons
    Eq, // ==
    Ne, // !=
    Lt, // <
    Gt, // >
    Le, // <=
    Ge, // >=

    // others, maybe not used
    At,         // @
    Underscore, // _
    DotDot,     // ..  for slices
    PathSep,    // ::
    Wildcard,   // ?
}

/// Implementation for TokenContent
impl TokenContent {
    pub fn to_str(tok: TokenContent) -> &'static str {
        match tok {
            // punctuations
            TokenContent::Dot => ".",
            TokenContent::Comma => ",",
            TokenContent::Colon => ":",
            TokenContent::SemiColon => ";",

            // delimiters
            TokenContent::LParen => "(",
            TokenContent::RParen => ")",
            TokenContent::LBrace => "{",
            TokenContent::RBrace => "}",
            TokenContent::LBracket => "[",
            TokenContent::RBracket => "]",

            // operators
            TokenContent::Plus => "+",
            TokenContent::Minus => "-",
            TokenContent::Star => "*",
            TokenContent::Slash => "/",
            TokenContent::Percent => "%",
            TokenContent::LShift => "<<",
            TokenContent::RShift => ">>",

            // bitwise operators
            TokenContent::Xor => "^",
            TokenContent::Not => "~",
            TokenContent::And => "&",
            TokenContent::Or => "|",

            // logical operators
            TokenContent::LNot => "!",
            TokenContent::LAnd => "&&",
            TokenContent::LOr => "||",

            // assignments
            TokenContent::Assign => "=",

            // arrows
            TokenContent::LArrow => "<-",
            TokenContent::RArrow => "->",
            TokenContent::BiDirArrow => "<->",
            TokenContent::FatArrow => "=>",
            TokenContent::BiDirFatArrow => "<=>",

            // comparisons
            TokenContent::Eq => "==",
            TokenContent::Ne => "!=",
            TokenContent::Lt => "<",
            TokenContent::Gt => ">",
            TokenContent::Le => "<=",
            TokenContent::Ge => ">=",

            // others, maybe not used
            TokenContent::At => "@",
            TokenContent::Underscore => "_",
            TokenContent::DotDot => "..",
            TokenContent::PathSep => "::",
            TokenContent::Wildcard => "?",
            TokenContent::Eof => "EOF",
            _ => panic!("unknown symbol for token {:?}", tok),
        }
    }
}

impl fmt::Debug for TokenContent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenContent::Keyword(_) => write!(f, "keyword"),
            TokenContent::Identifier(_) => write!(f, "identifier"),
            TokenContent::IntLiteral(_) => write!(f, "number"),
            TokenContent::BoolLiteral(_) => write!(f, "true, false"),
            t => write!(f, "{}", TokenContent::to_str(t.clone())),
        }
    }
}

/// Represents a lexed token.
#[derive(PartialEq, Debug, Clone)]
pub struct Token {
    /// the content of the token, defining its type
    pub content: TokenContent,

    /// the source position of the toke
    pub spos: SourcePos,
}

/// The Token Implementation
impl Token {
    /// Creats a new token with the given [TokenContent] at the [SourcePos].
    pub fn new(content: TokenContent, spos: SourcePos) -> Self {
        Token { content, spos }
    }

    /// Obtains the [SourcePos] of the token
    pub fn get_pos(&self) -> SourcePos {
        self.spos.clone()
    }
}

/// Implementation of the [std::fmt::Display] trait for [Token]
impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.content {
            TokenContent::Identifier(id) => write!(f, "{}", id),
            TokenContent::IntLiteral(n) => write!(f, "{}", n),
            TokenContent::BoolLiteral(bl) => write!(f, "{}", bl),
            TokenContent::Comment(st) => write!(f, "Comment({})", st),
            TokenContent::BlockComment(st) => write!(f, "BlockComment({})", st),
            TokenContent::Keyword(k) => write!(f, "{}", k),
            other => write!(f, "{}", TokenContent::to_str(other.clone())),
        }
    }
}

/// Implementation of `nom::InputLength` for `Token`
impl InputLength for Token {
    #[inline]
    /// Calculates the input length, as indicated by its name, and the name of the trait itself
    fn input_len(&self) -> usize {
        1
    }
}
