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

// used standard library modules
use std::convert::TryFrom;
use std::fmt;

// used nome components
use nom::InputLength;

// used crate modules
use crate::sourcepos::SourcePos;

/// Enumeration of all keywords in the language
#[derive(PartialEq, Debug, Clone, Copy)]
pub enum Keyword {
    //
    // language keywords
    //
    /// This token was originally used for unit definitions, It's not in use
    /// under the new unit scheme, but we're choosing to keep it as a reserved
    /// keyword for now.
    /// TODO: Will need to revisit this at somepoint -Ilias
    Unit,
    /// base type for static maps
    StaticMap,
    /// base type for direct segments
    Segment,

    //
    // Unit "fields"
    //
    /// the unit input bitwidth
    InBitWidth,
    /// the unit output bitwidth
    OutBitWidth,
    /// represents the "state field"
    State,
    /// interface statement
    Interface,

    //
    // State Kinds
    //
    /// in-memory state
    MemoryState,
    /// register backed state
    RegisterState,

    //
    // Interface Kinds
    //
    /// in-memory data structure interface
    MemoryInterface,
    /// memory mapped registers interface
    MMIOInterface,
    /// special purpose cpu register interface
    CPURegisterInterface,

    //
    // Interface descriptions
    //
    /// A read action from the interface on the state
    ReadAction,
    /// A write action from the interface on the state
    WriteAction,
    /// Used in identifying the Bitslice layout of an Interface field
    Layout,

    //
    // control flow and expressions
    //
    /// conditional statemt
    If,
    /// conditional else branch
    Else,
    /// for statements,
    For,
    /// defines a local variable
    Let,
    /// inclusion statement,
    In,
    /// represents a function
    Fn,
    /// the return keyword
    Return,

    //
    // types
    //
    /// represents an address value
    AddrType,
    /// represents a size value
    SizeType,
    /// A boolean type
    BooleanType,
    /// An integer value
    IntegerType,
    /// Represents the permission flags
    FlagsType,

    //
    // constraint keywords
    //
    /// the requires clause
    Requires,
    /// the ensures clause
    Ensures,
    /// An assert statement
    Assert,
    /// the forall quantifier
    Forall,
    /// the existential quantifier
    Exists,
    /// the invariant keyword
    Invariant,

    //
    // other keywords
    //
    /// constant values
    Const,
    /// import statements
    Import,
    /// Null-like value
    None,
}

impl Keyword {
    pub const fn as_str(&self) -> &str {
        match self {
            Keyword::Unit => "unit",
            Keyword::StaticMap => "staticmap",
            Keyword::Segment => "segment",
            //
            Keyword::InBitWidth => "inbitwidth",
            Keyword::OutBitWidth => "outbitwidth",
            Keyword::State => "state",
            Keyword::Interface => "interface",
            //
            Keyword::MemoryState => "MemoryState",
            Keyword::RegisterState => "RegisterState",
            Keyword::MemoryInterface => "MemoryInterface",
            Keyword::MMIOInterface => "MMIOInterface",
            Keyword::CPURegisterInterface => "CPURegisterInterface",
            //
            Keyword::ReadAction => "ReadAction",
            Keyword::WriteAction => "WriteAction",
            Keyword::Layout => "Layout",

            Keyword::If => "if",
            Keyword::Else => "else",
            Keyword::For => "for",
            Keyword::Let => "let",
            Keyword::In => "in",
            Keyword::Fn => "fn",
            Keyword::Return => "return",
            //
            Keyword::AddrType => "addr",
            Keyword::SizeType => "size",
            Keyword::BooleanType => "bool",
            Keyword::IntegerType => "int",
            Keyword::FlagsType => "flags",
            //
            Keyword::Requires => "requires",
            Keyword::Ensures => "ensures",
            Keyword::Assert => "assert",
            Keyword::Forall => "forall",
            Keyword::Exists => "exists",
            Keyword::Invariant => "invariant",
            //
            Keyword::Const => "const",
            Keyword::Import => "import",
            //
            Keyword::None => "None",
        }
    }
}

impl<'a> TryFrom<&'a str> for Keyword {
    type Error = &'a str;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        match value {
            "unit" => Ok(Keyword::Unit),
            "staticmap" => Ok(Keyword::StaticMap),
            "segment" => Ok(Keyword::Segment),
            //
            "inbitwidth" => Ok(Keyword::InBitWidth),
            "outbitwidth" => Ok(Keyword::OutBitWidth),
            "state" => Ok(Keyword::State),
            "interface" => Ok(Keyword::Interface),
            //
            "MemoryState" => Ok(Keyword::MemoryState),
            "RegisterState" => Ok(Keyword::RegisterState),
            "MemoryInterface" => Ok(Keyword::MemoryInterface),
            "MMIOInterface" => Ok(Keyword::MMIOInterface),
            "CPURegisterInterface" => Ok(Keyword::CPURegisterInterface),
            //
            "ReadAction" => Ok(Keyword::ReadAction),
            "WriteAction" => Ok(Keyword::WriteAction),
            "Layout" => Ok(Keyword::Layout),
            //
            "if" => Ok(Keyword::If),
            "else" => Ok(Keyword::Else),
            "for" => Ok(Keyword::For),
            "let" => Ok(Keyword::Let),
            "in" => Ok(Keyword::In),
            "fn" => Ok(Keyword::Fn),
            "return" => Ok(Keyword::Return),
            //
            "addr" => Ok(Keyword::AddrType),
            "size" => Ok(Keyword::SizeType),
            "bool" => Ok(Keyword::BooleanType),
            "int" => Ok(Keyword::IntegerType),
            "flags" => Ok(Keyword::FlagsType),
            "requires" => Ok(Keyword::Requires),
            "ensures" => Ok(Keyword::Ensures),
            "assert" => Ok(Keyword::Assert),
            "forall" => Ok(Keyword::Forall),
            "exists" => Ok(Keyword::Exists),
            "invariant" => Ok(Keyword::Invariant),
            //
            "const" => Ok(Keyword::Const),
            "import" => Ok(Keyword::Import),
            //
            "None" => Ok(Keyword::None),
            _ => Err(value),
        }
    }
}

/// Implementation of the [std::fmt::Display] trait for [Token]
impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
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
    RLongFatArrow, // ==>

    // comparisons
    Eq, // ==
    Ne, // !=
    Lt, // <
    Gt, // >
    Le, // <=
    Ge, // >=

    // others, maybe not used
    At,       // @
    DotDot,   // ..  for slices
    PathSep,  // ::
    Wildcard, // ?
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
            TokenContent::BiDirArrow => "<-->",
            TokenContent::FatArrow => "=>",
            TokenContent::BiDirFatArrow => "<=>",
            TokenContent::RLongFatArrow => "==>",

            // comparisons
            TokenContent::Eq => "==",
            TokenContent::Ne => "!=",
            TokenContent::Lt => "<",
            TokenContent::Gt => ">",
            TokenContent::Le => "<=",
            TokenContent::Ge => ">=",

            // others, maybe not used
            TokenContent::At => "@",
            TokenContent::DotDot => "..",
            TokenContent::PathSep => "::",
            TokenContent::Wildcard => "?",
            TokenContent::Eof => "EOF",

            // some other tokens
            TokenContent::IntLiteral(_) => panic!("INTEGER"),
            TokenContent::BoolLiteral(_) => panic!("BOOL"),
            TokenContent::Identifier(_) => panic!("IDENTIFIER"),
            TokenContent::Keyword(_) => panic!("KEYWORD"),
            TokenContent::Comment(_) => panic!("COMMENT"),
            TokenContent::BlockComment(_) => panic!("BLOCK COMMENT"),
            TokenContent::Illegal => panic!("illegal token"),
        }
    }

    /// returns true if the token is a keyword
    pub fn is_keyword(&self) -> bool {
        matches!(self, TokenContent::Keyword(_))
    }

    /// returns true if the token is a reserved identifier
    pub fn is_reserved(&self) -> bool {
        if let TokenContent::Identifier(ident) = self {
            matches!(
                ident.as_str(),
                // reserved indentifiers
                "Segment" | "StaticMap" |

                // for future use
                "abstract" | "while" | "matches"
            )
        } else {
            false
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

    /// returns true if the token is a keyword
    pub fn is_keyword(&self) -> bool {
        self.content.is_keyword()
    }

    /// returns true if the token is a reserved identifier
    pub fn is_reserved(&self) -> bool {
        self.content.is_reserved()
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

#[cfg(test)]
use std::convert::TryInto;

#[test]
fn test_enum_str() {

    // probably something like this would be enough:
    assert_eq!(Keyword::Unit.as_str().try_into(), Ok(Keyword::Unit));

    assert_eq!("unit".try_into(), Ok(Keyword::Unit));
    assert_eq!(Keyword::Unit.as_str(), "unit");
    assert_eq!("segment".try_into(), Ok(Keyword::Segment));
    assert_eq!(Keyword::Segment.as_str(), "segment");
    assert_eq!("staticmap".try_into(), Ok(Keyword::StaticMap));
    assert_eq!(Keyword::StaticMap.as_str(), "staticmap");

    assert_eq!("inbitwidth".try_into(), Ok(Keyword::InBitWidth));
    assert_eq!(Keyword::InBitWidth.as_str(), "inbitwidth");
    assert_eq!("outbitwidth".try_into(), Ok(Keyword::OutBitWidth));
    assert_eq!(Keyword::OutBitWidth.as_str(), "outbitwidth");
    assert_eq!("state".try_into(), Ok(Keyword::State));
    assert_eq!(Keyword::State.as_str(), "state");
    assert_eq!("interface".try_into(), Ok(Keyword::Interface));
    assert_eq!(Keyword::Interface.as_str(), "interface");

    assert_eq!("MemoryState".try_into(), Ok(Keyword::MemoryState));
    assert_eq!(Keyword::MemoryState.as_str(), "MemoryState");
    assert_eq!("RegisterState".try_into(), Ok(Keyword::RegisterState));
    assert_eq!(Keyword::RegisterState.as_str(), "RegisterState");

    assert_eq!("MemoryInterface".try_into(), Ok(Keyword::MemoryInterface));
    assert_eq!(Keyword::MemoryInterface.as_str(), "MemoryInterface");
    assert_eq!("MMIOInterface".try_into(), Ok(Keyword::MMIOInterface));
    assert_eq!(Keyword::MMIOInterface.as_str(), "MMIOInterface");
    assert_eq!(
        "CPURegisterInterface".try_into(),
        Ok(Keyword::CPURegisterInterface)
    );
    assert_eq!(
        Keyword::CPURegisterInterface.as_str(),
        "CPURegisterInterface"
    );

    assert_eq!("ReadAction".try_into(), Ok(Keyword::ReadAction));
    assert_eq!(Keyword::ReadAction.as_str(), "ReadAction");
    assert_eq!("WriteAction".try_into(), Ok(Keyword::WriteAction));
    assert_eq!(Keyword::WriteAction.as_str(), "WriteAction");
    assert_eq!("Layout".try_into(), Ok(Keyword::Layout));
    assert_eq!(Keyword::Layout.as_str(), "Layout");

    assert_eq!("if".try_into(), Ok(Keyword::If));
    assert_eq!(Keyword::If.as_str(), "if");
    assert_eq!("else".try_into(), Ok(Keyword::Else));
    assert_eq!(Keyword::Else.as_str(), "else");
    assert_eq!("for".try_into(), Ok(Keyword::For));
    assert_eq!(Keyword::For.as_str(), "for");
    assert_eq!("let".try_into(), Ok(Keyword::Let));
    assert_eq!(Keyword::Let.as_str(), "let");
    assert_eq!("in".try_into(), Ok(Keyword::In));
    assert_eq!(Keyword::In.as_str(), "in");
    assert_eq!("fn".try_into(), Ok(Keyword::Fn));
    assert_eq!(Keyword::Fn.as_str(), "fn");
    assert_eq!("return".try_into(), Ok(Keyword::Return));
    assert_eq!(Keyword::Return.as_str(), "return");

    assert_eq!("addr".try_into(), Ok(Keyword::AddrType));
    assert_eq!(Keyword::AddrType.as_str(), "addr");
    assert_eq!("size".try_into(), Ok(Keyword::SizeType));
    assert_eq!(Keyword::SizeType.as_str(), "size");
    assert_eq!("bool".try_into(), Ok(Keyword::BooleanType));
    assert_eq!(Keyword::BooleanType.as_str(), "bool");
    assert_eq!("int".try_into(), Ok(Keyword::IntegerType));
    assert_eq!(Keyword::IntegerType.as_str(), "int");
    assert_eq!("flags".try_into(), Ok(Keyword::FlagsType));
    assert_eq!(Keyword::FlagsType.as_str(), "flags");

    assert_eq!("requires".try_into(), Ok(Keyword::Requires));
    assert_eq!(Keyword::Requires.as_str(), "requires");
    assert_eq!("ensures".try_into(), Ok(Keyword::Ensures));
    assert_eq!(Keyword::Ensures.as_str(), "ensures");
    assert_eq!("invariant".try_into(), Ok(Keyword::Invariant));
    assert_eq!(Keyword::Invariant.as_str(), "invariant");
    assert_eq!("assert".try_into(), Ok(Keyword::Assert));
    assert_eq!(Keyword::Assert.as_str(), "assert");
    assert_eq!("forall".try_into(), Ok(Keyword::Forall));
    assert_eq!(Keyword::Forall.as_str(), "forall");
    assert_eq!("exists".try_into(), Ok(Keyword::Exists));
    assert_eq!(Keyword::Exists.as_str(), "exists");

    assert_eq!("const".try_into(), Ok(Keyword::Const));
    assert_eq!(Keyword::Const.as_str(), "const");
    assert_eq!("import".try_into(), Ok(Keyword::Import));
    assert_eq!(Keyword::Import.as_str(), "import");
    assert_eq!("None".try_into(), Ok(Keyword::None));
    assert_eq!(Keyword::None.as_str(), "None");
}
