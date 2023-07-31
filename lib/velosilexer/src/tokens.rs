// Velosilexer Token
//
//
// MIT License
//
// Copyright (c) 2021-2023 Systopia Lab, Computer Science, University of British Columbia
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
//! the lexing process, and that the parser will work on. Those tokens define
//! the type used in the TokenStream.

// used standard library modules
use std::convert::TryFrom;
use std::fmt::{Display, Formatter, Result as FmtResult};

// used external dependencies
use tokstream::TokKind;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Keywords
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Enumeration of all keywords in the Velosiraptor language
///
/// Each keyword is represented by a variant of this enum.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum VelosiKeyword {
    //
    // language keywords
    //
    /// constant values
    Const,
    /// import statements
    Import,
    /// base type for static maps
    StaticMap,
    /// base type for configurable segments
    Segment,
    /// base type for enum
    Enum,

    //
    // Unit "elements"
    //
    /// the unit input bitwidth
    InBitWidth,
    /// the unit output bitwidth
    OutBitWidth,
    /// represents the "state field"
    State,
    /// state definition
    StateDef,
    /// interface statement
    Interface,
    /// interface definition
    InterfaceDef,
    /// map definition
    MapDef,

    //
    // state & interface fields
    //
    /// field referring to a memory location
    Mem,
    /// field that is a register
    Reg,
    /// field that is a memory-mapped regsiter
    Mmio,

    //
    // interface descriptions
    //
    /// A read action block from the interface on the state
    ReadActions,
    /// A write action block from the interface on the state
    WriteActions,
    /// Bitfield layout description of an interface field
    Layout,

    //
    // method definition
    //
    /// represents a method
    Fn,
    /// indicates a synthesis target (function)
    Synth,
    /// unit or function that is abstract
    Abstract,

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
    /// the return keyword
    Return,

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
    // builtin types
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
    // other keywords
    //
    /// Null-like value
    None,
}

impl VelosiKeyword {
    /// Obtains the string slice representation of the keyword
    pub const fn as_str(&self) -> &'static str {
        match self {
            // language keywords
            VelosiKeyword::Const => "const",
            VelosiKeyword::Import => "import",
            VelosiKeyword::StaticMap => "staticmap",
            VelosiKeyword::Segment => "segment",
            VelosiKeyword::Enum => "enum",

            // Unit "elements"
            VelosiKeyword::InBitWidth => "inbitwidth",
            VelosiKeyword::OutBitWidth => "outbitwidth",
            VelosiKeyword::State => "state",
            VelosiKeyword::StateDef => "StateDef",
            VelosiKeyword::Interface => "interface",
            VelosiKeyword::InterfaceDef => "InterfaceDef",
            VelosiKeyword::MapDef => "mapdef",

            // state & interface fields
            VelosiKeyword::Mem => "mem",
            VelosiKeyword::Reg => "reg",
            VelosiKeyword::Mmio => "mmio",

            // interface descriptions
            VelosiKeyword::ReadActions => "ReadActions",
            VelosiKeyword::WriteActions => "WriteActions",
            VelosiKeyword::Layout => "Layout",

            // method definition
            VelosiKeyword::Fn => "fn",
            VelosiKeyword::Synth => "synth",
            VelosiKeyword::Abstract => "abstract",

            // control flow and expressions
            VelosiKeyword::If => "if",
            VelosiKeyword::Else => "else",
            VelosiKeyword::For => "for",
            VelosiKeyword::Let => "let",
            VelosiKeyword::In => "in",
            VelosiKeyword::Return => "return",

            // constraint keywords
            VelosiKeyword::Requires => "requires",
            VelosiKeyword::Ensures => "ensures",
            VelosiKeyword::Assert => "assert",
            VelosiKeyword::Forall => "forall",
            VelosiKeyword::Exists => "exists",
            VelosiKeyword::Invariant => "invariant",

            // built-intypes
            VelosiKeyword::AddressType => "addr",
            VelosiKeyword::VAddrType => "vaddr",
            VelosiKeyword::PAddrType => "paddr",
            VelosiKeyword::SizeType => "size",
            VelosiKeyword::BooleanType => "bool",
            VelosiKeyword::IntegerType => "int",
            VelosiKeyword::FlagsType => "flags",

            // other keywords
            VelosiKeyword::None => "None",
        }
    }
}

/// Implementation of [TryFrom] for [VelosiKeyword]
impl<'a> TryFrom<&'a str> for VelosiKeyword {
    type Error = &'a str;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        match value {
            // language keywords
            "const" => Ok(VelosiKeyword::Const),
            "import" => Ok(VelosiKeyword::Import),
            "staticmap" => Ok(VelosiKeyword::StaticMap),
            "segment" => Ok(VelosiKeyword::Segment),
            "enum" => Ok(VelosiKeyword::Enum),
            //  Unit "elements"
            "inbitwidth" => Ok(VelosiKeyword::InBitWidth),
            "outbitwidth" => Ok(VelosiKeyword::OutBitWidth),
            "state" => Ok(VelosiKeyword::State),
            "StateDef" => Ok(VelosiKeyword::StateDef),
            "interface" => Ok(VelosiKeyword::Interface),
            "InterfaceDef" => Ok(VelosiKeyword::InterfaceDef),
            "mapdef" => Ok(VelosiKeyword::MapDef),
            // state & interface fields
            "reg" => Ok(VelosiKeyword::Reg),
            "mem" => Ok(VelosiKeyword::Mem),
            "mmio" => Ok(VelosiKeyword::Mmio),
            //  interface descriptions
            "ReadActions" => Ok(VelosiKeyword::ReadActions),
            "WriteActions" => Ok(VelosiKeyword::WriteActions),
            "Layout" => Ok(VelosiKeyword::Layout),
            // method definition
            "fn" => Ok(VelosiKeyword::Fn),
            "synth" => Ok(VelosiKeyword::Synth),
            "abstract" => Ok(VelosiKeyword::Abstract),
            // control flow and expressions
            "if" => Ok(VelosiKeyword::If),
            "else" => Ok(VelosiKeyword::Else),
            "for" => Ok(VelosiKeyword::For),
            "let" => Ok(VelosiKeyword::Let),
            "in" => Ok(VelosiKeyword::In),
            "return" => Ok(VelosiKeyword::Return),
            // constraint keywords
            "requires" => Ok(VelosiKeyword::Requires),
            "ensures" => Ok(VelosiKeyword::Ensures),
            "assert" => Ok(VelosiKeyword::Assert),
            "forall" => Ok(VelosiKeyword::Forall),
            "exists" => Ok(VelosiKeyword::Exists),
            "invariant" => Ok(VelosiKeyword::Invariant),
            // builtin types
            "addr" => Ok(VelosiKeyword::AddressType),
            "vaddr" => Ok(VelosiKeyword::VAddrType),
            "paddr" => Ok(VelosiKeyword::PAddrType),
            "size" => Ok(VelosiKeyword::SizeType),
            "bool" => Ok(VelosiKeyword::BooleanType),
            "int" => Ok(VelosiKeyword::IntegerType),
            "flags" => Ok(VelosiKeyword::FlagsType),
            // other
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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Operator Tokens
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Operator Tokens representing the different operators and punctuations in the Velosiraptor Language
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
    HashTag,      // #
}

impl VelosiOpToken {
    /// Obtains the string slice representation of the operator token
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
            HashTag => "#",
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
impl<'a> TryFrom<&'a str> for VelosiOpToken {
    type Error = &'a str;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
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
            "#" => Ok(HashTag),

            _ => Err(value),
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Token Kind
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents the different Velosiraptor token kinds
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiTokenKind {
    /// represents an illegal token
    Illegal,
    /// A numeric literal (1234 0x134 0o1234 0b1111)
    NumLiteral(u64),
    /// a boolean literal (true | false)
    BoolLiteral(bool),
    /// an identifier (abc ab_cd)
    Identifier(String),
    /// a keyword token ([VelosiKeyword])
    Keyword(VelosiKeyword), //
    /// an operator token ([VelosiOpToken])
    OpToken(VelosiOpToken), //
    /// a single line comment token (// ... )
    Comment(String),
    /// a block comment token (/* */)
    BlockComment(String),
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
                "while" | "matches"
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
            Illegal => write!(f, "illegal token"),
            NumLiteral(n) => write!(f, "{n}"),
            BoolLiteral(n) => write!(f, "{n}"),
            Identifier(n) => write!(f, "{n}"),
            Keyword(n) => write!(f, "{n}"),
            Comment(n) => write!(f, "// {n}"),
            BlockComment(n) => write!(f, " /* {n} */"),
            OpToken(n) => write!(f, "{n}"),
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
                "while" | "matches"
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
    assert_eq!("segment".try_into(), Ok(VelosiKeyword::Segment));
    assert_eq!(VelosiKeyword::Segment.as_str(), "segment");
    assert_eq!("staticmap".try_into(), Ok(VelosiKeyword::StaticMap));
    assert_eq!(VelosiKeyword::StaticMap.as_str(), "staticmap");
    assert_eq!("enum".try_into(), Ok(VelosiKeyword::Enum));
    assert_eq!(VelosiKeyword::Enum.as_str(), "enum");

    assert_eq!("synth".try_into(), Ok(VelosiKeyword::Synth));
    assert_eq!(VelosiKeyword::Synth.as_str(), "synth");
    assert_eq!("abstract".try_into(), Ok(VelosiKeyword::Abstract));
    assert_eq!(VelosiKeyword::Abstract.as_str(), "abstract");

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

    assert_eq!("ReadActions".try_into(), Ok(VelosiKeyword::ReadActions));
    assert_eq!(VelosiKeyword::ReadActions.as_str(), "ReadActions");
    assert_eq!("WriteActions".try_into(), Ok(VelosiKeyword::WriteActions));
    assert_eq!(VelosiKeyword::WriteActions.as_str(), "WriteActions");
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
    assert_eq!("mapdef".try_into(), Ok(VelosiKeyword::MapDef));
    assert_eq!(VelosiKeyword::MapDef.as_str(), "mapdef");
    assert_eq!("import".try_into(), Ok(VelosiKeyword::Import));
    assert_eq!(VelosiKeyword::Import.as_str(), "import");
    assert_eq!("None".try_into(), Ok(VelosiKeyword::None));
    assert_eq!(VelosiKeyword::None.as_str(), "None");
}
