// Velosiraptor Parser
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

use std::fmt;

use crate::lexer::sourcepos::SourcePos;

///
/// Defines an import statement
///
#[derive(Debug, PartialEq, Clone)]
pub struct Import {
    pub name: String,
    pub pos: SourcePos,
}

impl Import {
    pub fn new(name: String, pos: SourcePos) -> Self {
        Import { name, pos }
    }
}

impl fmt::Display for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Import {}  ({:?})", self.name, self.pos.input_pos())
    }
}

///
/// Defines a translation unit
///
#[derive(Debug, PartialEq, Clone)]
pub struct Unit {
    pub name: String,
    pub derived: Option<String>,
    pub pos: SourcePos,
}

impl Unit {
    pub fn new(name: String, derived: Option<String>, pos: SourcePos) -> Self {
        Unit { name, derived, pos }
    }
}

impl fmt::Display for Unit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.derived {
            Some(n) => write!(
                f,
                "Unit {} : {}  ({:?})",
                self.name,
                n,
                self.pos.input_pos()
            ),
            None => write!(f, "Unit {}  ({:?})", self.name, self.pos.input_pos()),
        }
    }
}

// #[derive(Debug, PartialEq, Clone)]
// pub struct File {
//     pub filename: String,
//     pub imports: Vec<Import>,
//     pub units: Vec<Unit>,
// }

// impl File {
//     pub fn new(filename: String, imports: Vec<Import>, units: Vec<Unit>) -> Self {
//         File {
//             filename,
//             imports,
//             units,
//         }
//     }
// }

// impl fmt::Display for File {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         let mut imports = String::new();
//         imports.push_str("  Imports:\n");
//         for i in &self.imports {
//             imports.push_str(&format!("    {}\n", i))
//         }

//         let mut units = String::new();
//         units.push_str("  Units:");
//         for u in &self.units {
//             units.push_str(&format!("    {}\n", u))
//         }

//         write!(f, "File {}\n{}\n{}", self.filename, imports, units)
//     }
// }

#[derive(Debug, PartialEq, Clone)]
pub struct BitSlice {
    pub start: u16,
    pub end: u16,
    pub name: String,
    pub pos: SourcePos,
}

impl BitSlice {
    pub fn new(start: u16, end: u16, name: String, pos: SourcePos) -> Self {
        BitSlice {
            start,
            end,
            name,
            pos,
        }
    }
}

impl fmt::Display for BitSlice {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({:3}..{:3}, {})", self.start, self.end, &self.name)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Field {
    pub name: String,
    pub base: String,
    pub offset: u64,
    pub length: u64,
    pub slices: Vec<BitSlice>,
    pub pos: SourcePos,
}

impl Field {
    pub fn new(
        name: String,
        base: String,
        offset: u64,
        length: u64,
        slices: Vec<BitSlice>,
        pos: SourcePos,
    ) -> Self {
        Field {
            name,
            base,
            offset,
            length,
            slices,
            pos,
        }
    }
}

impl fmt::Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut entries = String::new();

        for b in &self.slices {
            entries.push_str(&format!("    {}\n", b))
        }

        write!(
            f,
            "    {} [{}, {}, {}] {{\n {}    }};\n",
            self.name, self.base, self.offset, self.length, entries
        )
    }
}

/// Binary operations
#[derive(Debug, PartialEq, Clone)]
pub enum BinOp {
    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
    LShift,
    RShift,
    And,
    Xor,
    Or,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    Land,
    Lor,
}

impl fmt::Display for BinOp {
    fn fmt(&self, format: &mut fmt::Formatter) -> fmt::Result {
        use self::BinOp::*;
        match self {
            Plus => write!(format, "+"),
            Minus => write!(format, "-"),
            Multiply => write!(format, "*"),
            Divide => write!(format, "/"),
            Modulo => write!(format, "%"),
            LShift => write!(format, "<<"),
            RShift => write!(format, ">>"),
            And => write!(format, "&"),
            Xor => write!(format, "^"),
            Or => write!(format, "|"),
            Eq => write!(format, "=="),
            Ne => write!(format, "!="),
            Lt => write!(format, "<"),
            Gt => write!(format, ">"),
            Le => write!(format, "<="),
            Ge => write!(format, ">="),
            Land => write!(format, "&&"),
            Lor => write!(format, "||"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum UnOp {
    Not,
    LNot,
    Ref,
}

impl fmt::Display for UnOp {
    fn fmt(&self, format: &mut fmt::Formatter) -> fmt::Result {
        use self::UnOp::*;
        match self {
            Not => write!(format, "~"),
            LNot => write!(format, "!"),
            Ref => write!(format, "&"),
        }
    }
}

use std::ops::Range;

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Identifier {
        path: Vec<String>,
        pos: SourcePos,
    },
    Number {
        value: u64,
        pos: SourcePos,
    },
    Boolean {
        value: bool,
        pos: SourcePos,
    },
    BinaryOperation {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        pos: SourcePos,
    },
    UnaryOperation {
        op: UnOp,
        val: Box<Expr>,
        pos: SourcePos,
    },
    FnCall {
        path: Vec<String>,
        pos: SourcePos,
    },
    Slice {
        path: Vec<String>,
        slice: Box<Expr>,
        pos: SourcePos,
    },
}

impl fmt::Display for Expr {
    fn fmt(&self, format: &mut fmt::Formatter) -> fmt::Result {
        use self::Expr::*;
        match self {
            Identifier { path, pos } => write!(format, "{}", path.join(".")),
            Number { value, pos } => write!(format, "{}", value),
            Boolean { value, pos } => write!(format, "{}", value),
            BinaryOperation { op, lhs, rhs, pos } => write!(format, "({} {} {})", lhs, op, rhs),
            UnaryOperation { op, val, pos } => write!(format, "{}({})", op, val),
            FnCall { path, pos } => write!(format, "foo"),
            Slice { path, slice, pos } => write!(format, "foo"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Stmt {
    pos: SourcePos,
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "STATEMENT (TODO) @ {};\n", self.pos)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Const {
    ident: String,
    value: u64,
    pos: SourcePos,
}

impl Const {
    pub fn new(ident: String, value: u64, pos: SourcePos) -> Self {
        Const { ident, value, pos }
    }
}
// pub enum State {
//     MemoryState {
//         bases: Vec<String>,
//         fields: Vec<StateField>,
//         pos: (u32, u32),
//     },
//     RegisterState {
//         bases: Vec<String>,
//         fields: Vec<StateField>,
//         pos: (u32, u32),
//     },
//     Dummy,
// }

/// represents the parsed Ast
pub struct Ast {}

impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Ast: TODO",)
    }
}
