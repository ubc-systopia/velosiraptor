// Velosilexer Token
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

//! # Velosilexer Tokens
//!
//! The VelosiLexer Tokens represent the language tokens that are produces by
//! the lexing process, and that the parser will work on.

// used standard library modules
use std::convert::TryFrom;
use std::fmt::{Display, Formatter, Result as FmtResult};

// used external dependencies
use crate::TokKind;

/// Enumeration of all keywords in the language
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum VelosiKeyword {
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
    /// state definition
    StateDef,
    InterfaceDef,

    //
    // State / Interface Fields
    //
    /// field referring to a memory location
    Mem,
    /// field that is a register
    Reg,
    /// field that is a memory-mapped regsiter
    Mmio,

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
    /// represents the generic address type
    AddressType,
    /// represents a virtual address value type
    VAddrType,
    /// represents a physical address value type
    PAddrType,
    /// represents a size value type
    SizeType,
    /// A boolean type
    BooleanType,
    /// An generic integer value type
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

impl VelosiKeyword {
    pub const fn as_str(&self) -> &'static str {
        match self {
            VelosiKeyword::Unit => "unit",
            VelosiKeyword::StaticMap => "staticmap",
            VelosiKeyword::Segment => "segment",
            //
            VelosiKeyword::InBitWidth => "inbitwidth",
            VelosiKeyword::OutBitWidth => "outbitwidth",
            VelosiKeyword::State => "state",
            VelosiKeyword::Interface => "interface",

            VelosiKeyword::StateDef => "StateDef",
            VelosiKeyword::InterfaceDef => "InterfaceDef",

            VelosiKeyword::Mem => "mem",
            VelosiKeyword::Reg => "reg",
            VelosiKeyword::Mmio => "mmio",

            //
            VelosiKeyword::ReadAction => "ReadAction",
            VelosiKeyword::WriteAction => "WriteAction",
            VelosiKeyword::Layout => "Layout",

            VelosiKeyword::If => "if",
            VelosiKeyword::Else => "else",
            VelosiKeyword::For => "for",
            VelosiKeyword::Let => "let",
            VelosiKeyword::In => "in",
            VelosiKeyword::Fn => "fn",
            VelosiKeyword::Return => "return",
            //
            VelosiKeyword::AddressType => "addr",
            VelosiKeyword::VAddrType => "vaddr",
            VelosiKeyword::PAddrType => "paddr",
            VelosiKeyword::SizeType => "size",
            VelosiKeyword::BooleanType => "bool",
            VelosiKeyword::IntegerType => "int",
            VelosiKeyword::FlagsType => "flags",
            //
            VelosiKeyword::Requires => "requires",
            VelosiKeyword::Ensures => "ensures",
            VelosiKeyword::Assert => "assert",
            VelosiKeyword::Forall => "forall",
            VelosiKeyword::Exists => "exists",
            VelosiKeyword::Invariant => "invariant",
            //
            VelosiKeyword::Const => "const",
            VelosiKeyword::Import => "import",
            //
            VelosiKeyword::None => "None",
        }
    }
}

impl<'a> TryFrom<&'a str> for VelosiKeyword {
    type Error = &'a str;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        match value {
            "unit" => Ok(VelosiKeyword::Unit),
            "staticmap" => Ok(VelosiKeyword::StaticMap),
            "segment" => Ok(VelosiKeyword::Segment),
            //
            "inbitwidth" => Ok(VelosiKeyword::InBitWidth),
            "outbitwidth" => Ok(VelosiKeyword::OutBitWidth),
            "state" => Ok(VelosiKeyword::State),
            "interface" => Ok(VelosiKeyword::Interface),
            //
            "StateDef" => Ok(VelosiKeyword::StateDef),
            "InterfaceDef" => Ok(VelosiKeyword::InterfaceDef),
            //
            "reg" => Ok(VelosiKeyword::Reg),
            "mem" => Ok(VelosiKeyword::Mem),
            "mmio" => Ok(VelosiKeyword::Mmio),
            //
            "ReadAction" => Ok(VelosiKeyword::ReadAction),
            "WriteAction" => Ok(VelosiKeyword::WriteAction),
            "Layout" => Ok(VelosiKeyword::Layout),
            //
            "if" => Ok(VelosiKeyword::If),
            "else" => Ok(VelosiKeyword::Else),
            "for" => Ok(VelosiKeyword::For),
            "let" => Ok(VelosiKeyword::Let),
            "in" => Ok(VelosiKeyword::In),
            "fn" => Ok(VelosiKeyword::Fn),
            "return" => Ok(VelosiKeyword::Return),
            //
            "addr" => Ok(VelosiKeyword::AddressType),
            "vaddr" => Ok(VelosiKeyword::VAddrType),
            "paddr" => Ok(VelosiKeyword::PAddrType),
            "size" => Ok(VelosiKeyword::SizeType),
            "bool" => Ok(VelosiKeyword::BooleanType),
            "int" => Ok(VelosiKeyword::IntegerType),
            "flags" => Ok(VelosiKeyword::FlagsType),
            "requires" => Ok(VelosiKeyword::Requires),
            "ensures" => Ok(VelosiKeyword::Ensures),
            "assert" => Ok(VelosiKeyword::Assert),
            "forall" => Ok(VelosiKeyword::Forall),
            "exists" => Ok(VelosiKeyword::Exists),
            "invariant" => Ok(VelosiKeyword::Invariant),
            //
            "const" => Ok(VelosiKeyword::Const),
            "import" => Ok(VelosiKeyword::Import),
            //
            "None" => Ok(VelosiKeyword::None),
            _ => Err(value),
        }
    }
}

/// Implementation of the [Display] trait for [VelosiKeyword]
impl Display for VelosiKeyword {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", self.as_str())
    }
}

/// Operator Tokens
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum VelosiOpToken {
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
    Percent, // %
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
    At,           // @
    DotDot,       // ..
    ColonColon,   // ::
    QuestionMark, // ?
}

impl VelosiOpToken {
    pub fn as_str(&self) -> &'static str {
        use VelosiOpToken::*;
        match self {
            // punctuations
            Dot => ".",
            Comma => ",",
            Colon => ":",
            SemiColon => ";",

            // delimiters
            LParen => "(",
            RParen => ")",
            LBrace => "{",
            RBrace => "}",
            LBracket => "[",
            RBracket => "]",

            // operators
            Plus => "+",
            Minus => "-",
            Star => "*",
            Slash => "/",
            Percent => "%",
            LShift => "<<",
            RShift => ">>",

            // bitwise operators
            Xor => "^",
            Not => "~",
            And => "&",
            Or => "|",

            // logical operators
            LNot => "!",
            LAnd => "&&",
            LOr => "||",

            // assignments
            Assign => "=",

            // arrows
            LArrow => "<-",
            RArrow => "->",
            BiDirArrow => "<-->",
            FatArrow => "=>",
            BiDirFatArrow => "<=>",
            RLongFatArrow => "==>",

            // comparisons
            Eq => "==",
            Ne => "!=",
            Lt => "<",
            Gt => ">",
            Le => "<=",
            Ge => ">=",

            // others, maybe not used
            At => "@",
            DotDot => "..",
            ColonColon => "::",
            QuestionMark => "?",
        }
    }
}

/// Implementation of the [Display] trait for [VelosiOpToken]
impl Display for VelosiOpToken {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", self.as_str())
    }
}

/// Implementation of the [TryFrom<&str>] trait for [VelosiOpToken]
impl TryFrom<&str> for VelosiOpToken {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        use VelosiOpToken::*;
        match value {
            // punctuations
            "." => Ok(Dot),
            "," => Ok(Comma),
            ":" => Ok(Colon),
            ";" => Ok(SemiColon),

            // delimiters
            "(" => Ok(LParen),
            ")" => Ok(RParen),
            "{" => Ok(LBrace),
            "}" => Ok(RBrace),
            "[" => Ok(LBracket),
            "]" => Ok(RBracket),

            // operators
            "+" => Ok(Plus),
            "-" => Ok(Minus),
            "*" => Ok(Star),
            "/" => Ok(Slash),
            "%" => Ok(Percent),
            "<<" => Ok(LShift),
            ">>" => Ok(RShift),

            // bitwise operators
            "^" => Ok(Xor),
            "~" => Ok(Not),
            "&" => Ok(And),
            "|" => Ok(Or),

            // logical operators
            "!" => Ok(LNot),
            "&&" => Ok(LAnd),
            "||" => Ok(LOr),

            // assignments
            "=" => Ok(Assign),

            // arrows
            "<-" => Ok(LArrow),
            "->" => Ok(RArrow),
            "<->" => Ok(BiDirArrow),
            "=>" => Ok(FatArrow),
            "<=>" => Ok(BiDirFatArrow),
            "==>" => Ok(RLongFatArrow),

            // comparisons
            "==" => Ok(Eq),
            "!=" => Ok(Ne),
            "<" => Ok(Lt),
            ">" => Ok(Gt),
            "<=" => Ok(Le),
            ">=" => Ok(Ge),

            // others, maybe not used
            "@" => Ok(At),
            ".." => Ok(DotDot),
            "::" => Ok(ColonColon),
            "?" => Ok(QuestionMark),

            _ => Err(()),
        }
    }
}

/// Represents the content of a token
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiTokenKind {
    // illegal token
    Illegal,

    // literals, integers of booleans
    NumLiteral(u64),   // 1234 0x134 0o1234 0b1111
    BoolLiteral(bool), // true | false

    // identifier
    Identifier(String), // abc ab_cd

    // Keywords
    Keyword(VelosiKeyword),

    // comments
    Comment(String),      // //
    BlockComment(String), // /* */

    OpToken(VelosiOpToken),
}

/// Implementation for VelosiTokenKind
impl VelosiTokenKind {
    /// returns true if the token is a keyword
    pub fn is_keyword(&self) -> bool {
        matches!(self, VelosiTokenKind::Keyword(_))
    }

    /// returns true if the token is a reserved identifier
    pub fn is_reserved(&self) -> bool {
        if let VelosiTokenKind::Identifier(ident) = self {
            matches!(
                ident.as_str(),
                // for future use
                "abstract" | "while" | "matches"
            )
        } else {
            false
        }
    }

    pub fn as_hint_str(&self) -> &'static str {
        use VelosiTokenKind::*;
        match self {
            Illegal => "illegal token",
            NumLiteral(_) => "integer literal",
            BoolLiteral(_) => "boolean literal",
            Identifier(_) => "identifier",
            Keyword(keyword) => keyword.as_str(),
            Comment(_) => "comment",
            BlockComment(_) => "block comment",
            OpToken(op_token) => op_token.as_str(),
        }
    }
}

impl Display for VelosiTokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use VelosiTokenKind::*;
        match self {
            Illegal => write!(f, "Illegal"),
            NumLiteral(n) => write!(f, "{}", n),
            BoolLiteral(n) => write!(f, "{}", n),
            Identifier(n) => write!(f, "{}", n),
            Keyword(n) => write!(f, "{}", n),
            Comment(n) => write!(f, "// {}", n),
            BlockComment(n) => write!(f, " /* {} */", n),
            OpToken(n) => write!(f, "{}", n),
        }
    }
}

impl TokKind for VelosiTokenKind {
    /// whether the token is a keyword
    fn is_keyword(&self) -> bool {
        matches!(self, VelosiTokenKind::Keyword(_))
    }

    /// whether the token has a reserved value
    fn is_reserved(&self) -> bool {
        if let VelosiTokenKind::Identifier(ident) = self {
            matches!(
                ident.as_str(),
                // for future use
                "abstract" | "while" | "matches"
            )
        } else {
            false
        }
    }

    /// whether the token is a comment
    fn is_comment(&self) -> bool {
        matches!(
            self,
            VelosiTokenKind::Comment(_) | VelosiTokenKind::BlockComment(_)
        )
    }

    /// whether the token is a literal, string or number, keyword, ...
    fn is_literal(&self) -> bool {
        matches!(
            self,
            VelosiTokenKind::NumLiteral(_)
                | VelosiTokenKind::BoolLiteral(_)
                | VelosiTokenKind::Keyword(_)
        )
    }

    /// whether the token is an identifier
    fn is_identifier(&self) -> bool {
        matches!(self, VelosiTokenKind::Identifier(_))
    }

    /// whether or not to keep the token when filtering it
    fn keep(&self) -> bool {
        !self.is_comment()
    }
}

#[cfg(test)]
use std::convert::TryInto;

#[test]
fn test_enum_str() {
    // probably something like this would be enough:
    assert_eq!(
        VelosiKeyword::Unit.as_str().try_into(),
        Ok(VelosiKeyword::Unit)
    );

    assert_eq!("unit".try_into(), Ok(VelosiKeyword::Unit));
    assert_eq!(VelosiKeyword::Unit.as_str(), "unit");
    assert_eq!("segment".try_into(), Ok(VelosiKeyword::Segment));
    assert_eq!(VelosiKeyword::Segment.as_str(), "segment");
    assert_eq!("staticmap".try_into(), Ok(VelosiKeyword::StaticMap));
    assert_eq!(VelosiKeyword::StaticMap.as_str(), "staticmap");

    assert_eq!("inbitwidth".try_into(), Ok(VelosiKeyword::InBitWidth));
    assert_eq!(VelosiKeyword::InBitWidth.as_str(), "inbitwidth");
    assert_eq!("outbitwidth".try_into(), Ok(VelosiKeyword::OutBitWidth));
    assert_eq!(VelosiKeyword::OutBitWidth.as_str(), "outbitwidth");
    assert_eq!("state".try_into(), Ok(VelosiKeyword::State));
    assert_eq!(VelosiKeyword::State.as_str(), "state");
    assert_eq!("interface".try_into(), Ok(VelosiKeyword::Interface));
    assert_eq!(VelosiKeyword::Interface.as_str(), "interface");

    assert_eq!("StateDef".try_into(), Ok(VelosiKeyword::StateDef));
    assert_eq!(VelosiKeyword::StateDef.as_str(), "StateDef");
    assert_eq!("InterfaceDef".try_into(), Ok(VelosiKeyword::InterfaceDef));

    assert_eq!("mem".try_into(), Ok(VelosiKeyword::Mem));
    assert_eq!(VelosiKeyword::Mem.as_str(), "mem");
    assert_eq!("reg".try_into(), Ok(VelosiKeyword::Reg));
    assert_eq!(VelosiKeyword::Reg.as_str(), "reg");
    assert_eq!("mmio".try_into(), Ok(VelosiKeyword::Mmio));
    assert_eq!(VelosiKeyword::Mmio.as_str(), "mmio");

    assert_eq!("ReadAction".try_into(), Ok(VelosiKeyword::ReadAction));
    assert_eq!(VelosiKeyword::ReadAction.as_str(), "ReadAction");
    assert_eq!("WriteAction".try_into(), Ok(VelosiKeyword::WriteAction));
    assert_eq!(VelosiKeyword::WriteAction.as_str(), "WriteAction");
    assert_eq!("Layout".try_into(), Ok(VelosiKeyword::Layout));
    assert_eq!(VelosiKeyword::Layout.as_str(), "Layout");

    assert_eq!("if".try_into(), Ok(VelosiKeyword::If));
    assert_eq!(VelosiKeyword::If.as_str(), "if");
    assert_eq!("else".try_into(), Ok(VelosiKeyword::Else));
    assert_eq!(VelosiKeyword::Else.as_str(), "else");
    assert_eq!("for".try_into(), Ok(VelosiKeyword::For));
    assert_eq!(VelosiKeyword::For.as_str(), "for");
    assert_eq!("let".try_into(), Ok(VelosiKeyword::Let));
    assert_eq!(VelosiKeyword::Let.as_str(), "let");
    assert_eq!("in".try_into(), Ok(VelosiKeyword::In));
    assert_eq!(VelosiKeyword::In.as_str(), "in");
    assert_eq!("fn".try_into(), Ok(VelosiKeyword::Fn));
    assert_eq!(VelosiKeyword::Fn.as_str(), "fn");
    assert_eq!("return".try_into(), Ok(VelosiKeyword::Return));
    assert_eq!(VelosiKeyword::Return.as_str(), "return");

    assert_eq!("addr".try_into(), Ok(VelosiKeyword::AddressType));
    assert_eq!(VelosiKeyword::AddressType.as_str(), "addr");
    assert_eq!("vaddr".try_into(), Ok(VelosiKeyword::VAddrType));
    assert_eq!(VelosiKeyword::VAddrType.as_str(), "vaddr");
    assert_eq!("paddr".try_into(), Ok(VelosiKeyword::PAddrType));
    assert_eq!(VelosiKeyword::PAddrType.as_str(), "paddr");
    assert_eq!("size".try_into(), Ok(VelosiKeyword::SizeType));
    assert_eq!(VelosiKeyword::SizeType.as_str(), "size");
    assert_eq!("bool".try_into(), Ok(VelosiKeyword::BooleanType));
    assert_eq!(VelosiKeyword::BooleanType.as_str(), "bool");
    assert_eq!("int".try_into(), Ok(VelosiKeyword::IntegerType));
    assert_eq!(VelosiKeyword::IntegerType.as_str(), "int");
    assert_eq!("flags".try_into(), Ok(VelosiKeyword::FlagsType));
    assert_eq!(VelosiKeyword::FlagsType.as_str(), "flags");

    assert_eq!("requires".try_into(), Ok(VelosiKeyword::Requires));
    assert_eq!(VelosiKeyword::Requires.as_str(), "requires");
    assert_eq!("ensures".try_into(), Ok(VelosiKeyword::Ensures));
    assert_eq!(VelosiKeyword::Ensures.as_str(), "ensures");
    assert_eq!("invariant".try_into(), Ok(VelosiKeyword::Invariant));
    assert_eq!(VelosiKeyword::Invariant.as_str(), "invariant");
    assert_eq!("assert".try_into(), Ok(VelosiKeyword::Assert));
    assert_eq!(VelosiKeyword::Assert.as_str(), "assert");
    assert_eq!("forall".try_into(), Ok(VelosiKeyword::Forall));
    assert_eq!(VelosiKeyword::Forall.as_str(), "forall");
    assert_eq!("exists".try_into(), Ok(VelosiKeyword::Exists));
    assert_eq!(VelosiKeyword::Exists.as_str(), "exists");

    assert_eq!("const".try_into(), Ok(VelosiKeyword::Const));
    assert_eq!(VelosiKeyword::Const.as_str(), "const");
    assert_eq!("import".try_into(), Ok(VelosiKeyword::Import));
    assert_eq!(VelosiKeyword::Import.as_str(), "import");
    assert_eq!("None".try_into(), Ok(VelosiKeyword::None));
    assert_eq!(VelosiKeyword::None.as_str(), "None");
}
