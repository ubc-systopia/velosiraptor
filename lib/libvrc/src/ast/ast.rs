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

//! Ast representation of the VelosiRaptor Definitions

use std::fmt;

// we use the source position to tag the elements of the AST
use crate::lexer::sourcepos::SourcePos;

/// represents the known types.
///
/// The type of a an expression, parameter or value defines the set of
/// operations that are allowed to be carried out with it.
pub enum Type {
    /// a boolean type (true / false)
    Boolean,
    /// An integer type
    Integer,
    /// Represents an address value
    Address,
    /// The size defines the number of addresses within a range
    Size,
}

/// represents the ast of a parsed file.
///
/// The parsed file consists of three possible directives:
///   1. imports: references to other files
///   2. constants: pre-defined values
///   3. units: units defined in this file
#[derive(PartialEq, Clone)]
pub struct Ast {
    /// the filename this ast represents
    pub filename: String,
    /// the import statements found in the Ast
    pub imports: Vec<Import>,
    /// the declared constants
    pub consts: Vec<String>,
    /// the defined units of in the AST
    pub units: Vec<String>,
}

/// implementation of the [fmt::Display] trait for the [Ast].
impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Ast: TODO",)
    }
}

/// implementation of the [fmt::Debug] display trait for the [Ast].
impl fmt::Debug for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Ast: TODO",)
    }
}

/// Defines an [Import] statement node
///
/// The import statement declares that another file is imported
/// and its definitions used by the current file.
#[derive(PartialEq, Clone)]
pub struct Import {
    /// the filename to import
    pub name: String,
    /// where in the current file there was this import statement
    pub pos: SourcePos,
}

/// implementation of the Display trait for the Ast
impl fmt::Display for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "import {};", self.name)
    }
}

/// implementation of the [fmt::Debug] trait for the [Import]
impl fmt::Debug for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.pos.input_pos();
        write!(f, "{:03}:{:03} | import {};", line, column, self.name)
    }
}

/// Defines a [Constant] statement node
///
/// The constants statement defines and delcares specific symbols
/// with constant values to be used throughout the definitions.
///
/// The constant can be defined as part of the file global definitions
/// or within a unit context.
#[derive(PartialEq, Clone)]
pub enum Const {
    /// Represents an integer constant.
    ///
    /// This corresponds to an Integer literal
    Integer {
        ident: String,
        value: u64,
        pos: SourcePos,
    },
    /// Represents an boolean constant
    ///
    /// This corresponds to an Boolean literal
    Boolean {
        ident: String,
        value: bool,
        pos: SourcePos,
    }, // TODO: add address / size constants here as well?
}

/// implementation of the Display trait for the Ast
impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Const::*;
        match self {
            Integer { ident, value, pos } => write!(f, "const {} : int  = {};", ident, value),
            Boolean { ident, value, pos } => write!(f, "const {} : bool = {};", ident, value),
        }
    }
}

/// implementation of the [fmt::Debug] trait for the [Import]
impl fmt::Debug for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Const::*;
        match self {
            Integer { ident, value, pos } => {
                let (line, column) = pos.input_pos();
                write!(
                    f,
                    "{:03}:{:03} | const {} :  int = {};",
                    line, column, ident, value
                )
            }
            Boolean { ident, value, pos } => {
                let (line, column) = pos.input_pos();
                write!(
                    f,
                    "{:03}:{:03} | const {} : bool = {};",
                    line, column, ident, value
                )
            }
        }
    }
}

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
pub enum Stmt {
    Block {
        stmts: Vec<Stmt>,
        pos: SourcePos,
    },
    Assign {
        lhs: String,
        rhs: Expr,
        pos: SourcePos,
    },
    IfElse {
        cond: Expr,
        then: Box<Stmt>,
        other: Option<Box<Stmt>>,
        pos: SourcePos,
    },
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Stmt::*;
        match self {
            Block { stmts, pos } => {
                write!(f, "{{ {} }} \n", "TODO")
            }
            Assign { lhs, rhs, pos } => write!(f, "let {} = {};\n", rhs, rhs),
            IfElse {
                cond,
                then,
                other,
                pos,
            } => match other {
                None => write!(f, "if {} {} \n", cond, then),
                Some(x) => write!(f, "if {} {} else {} \n", cond, then, x),
            },
        }
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
