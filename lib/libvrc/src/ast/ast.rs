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
#[derive(PartialEq, Clone, Copy)]
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

/// implementation of the [fmt::Display] trait for the [Type].
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Type::*;
        match self {
            Boolean => write!(f, "bool"),
            Integer => write!(f, "int"),
            Address => write!(f, "addr"),
            Size => write!(f, "size"),
        }
    }
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
        writeln!(f, "Ast: TODO",)
    }
}

/// implementation of the [fmt::Debug] display trait for the [Ast].
impl fmt::Debug for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Ast: TODO",)
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

/// implementation of the [fmt::Display] trait for the [Import]
impl fmt::Display for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "import {};", self.name)
    }
}

/// implementation of the [fmt::Debug] trait for the [Import]
impl fmt::Debug for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.pos.input_pos();
        writeln!(f, "{:03}:{:03} | import {};", line, column, self.name)
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

/// implementation of the [fmt::Display] trait for the [Const]
impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Const::*;
        match self {
            Integer {
                ident,
                value,
                pos: _,
            } => writeln!(f, "const {} : int  = {};", ident, value),
            Boolean {
                ident,
                value,
                pos: _,
            } => writeln!(f, "const {} : bool = {};", ident, value),
        }
    }
}

/// implementation of the [fmt::Debug] trait for the [Const]
impl fmt::Debug for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Const::*;
        match self {
            Integer { ident, value, pos } => {
                let (line, column) = pos.input_pos();
                writeln!(
                    f,
                    "{:03}:{:03} | const {} :  int = {};",
                    line, column, ident, value
                )
            }
            Boolean { ident, value, pos } => {
                let (line, column) = pos.input_pos();
                writeln!(
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
/// A translation unit describes a translation unit and consists of multiple
/// components that from the personality of the translation unit.
///
/// Moreover, a translation unit may be derived from another unit, similar
/// to inheritance in other languages.
#[derive(PartialEq, Clone)]
pub struct Unit {
    /// the name of the unit (identifier)
    pub name: String,
    /// the name of the derrived unit
    pub derived: Option<String>,
    /// defined constants in this unit
    pub consts: Vec<Const>,
    /// the state of the unit
    pub state: State,
    /// the software visible interface of the unit
    pub interface: Interface,
    /// the methods defined by this unit
    pub methods: Vec<Method>,
    // TODO: maybe make the translate / constructors / map / ... explicit here?
    /// the position in the source tree where this unit is defined
    pub pos: SourcePos,
}

/// implementation of the [fmt::Display] trait for the [Unit]
impl fmt::Display for Unit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.derived {
            Some(n) => writeln!(f, "Unit {} : {}  {{\nTODO\n}}", self.name, n),
            None => writeln!(f, "Unit {} {{\nTODO\n}}", self.name),
        }
    }
}

/// implementation of the [fmt::Debug] trait for the [Unit]
impl fmt::Debug for Unit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.pos.input_pos();
        match &self.derived {
            Some(n) => writeln!(
                f,
                "{:03}:{:03} | unit {} : {}  {{\nTODO\n}}",
                line, column, self.name, n
            ),
            None => writeln!(
                f,
                "{:03}:{:03} | unit {} {{\nTODO\n}}",
                line, column, self.name
            ),
        }
    }
}

/// Defines the state of a translation unit
///
/// The State defines how the translation unit will translate incoming addresses.
/// There are three fundamental state types:
///   - Memory: the state is *external* to the translation unit in some memory (e.g, RAM)
///   - Register: the state is *internal* to the translation unit
///   - None: there is no state associated with it.
#[derive(PartialEq, Clone)]
pub enum State {
    /// defines a memory state (external to the unit)
    MemoryState {
        /// a list of identifiers referring to memory regions
        bases: Vec<String>,
        /// defines a list of fields within the memory regions, defined by the bases
        fields: Vec<Field>,
        /// position where this state was defined
        pos: SourcePos,
    },
    /// defines a register state (internal to the unit)
    RegisterState {
        /// defines a list of fields that form the state
        fields: Vec<Field>,
        /// the position where the state is defined
        pos: SourcePos,
    },
    // TODO state that may be combined
    //CombinedState {  },
    /// No state associated with this translation unit
    None,
}

/// implementation of the [fmt::Display] trait for the [State]
impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::State::*;
        match self {
            MemoryState { bases, fields, pos } => {
                write!(f, "State(Memory) [")?;
                bases
                    .iter()
                    .fold(Ok(()), |result, b| result.and_then(|_| write!(f, "{} ", b)))?;
                writeln!(f, "] {{")?;

                fields.iter().fold(Ok(()), |result, field| {
                    result.and_then(|_| writeln!(f, "{}", field))
                })?;
                writeln!(f, "}}")
            }
            RegisterState { fields, pos } => {
                let s = String::new();
                writeln!(f, "State(Registers) {{")?;
                fields.iter().fold(Ok(()), |result, field| {
                    result.and_then(|_| writeln!(f, "{}", field))
                })?;
                writeln!(f, "}}")
            }
            None => writeln!(f, "State(None)"),
        }
    }
}

/// implementation of the [fmt::Debug] trait for the [State]
impl fmt::Debug for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::State::*;
        //let (line, column) = self.pos.input_pos();
        match self {
            MemoryState { bases, fields, pos } => {
                let (line, column) = pos.input_pos();
                write!(f, "{:03}:{:03} | State(Memory) [", line, column)?;
                bases
                    .iter()
                    .fold(Ok(()), |result, b| result.and_then(|_| write!(f, "{} ", b)))?;
                writeln!(f, "] {{")?;

                fields.iter().fold(Ok(()), |result, field| {
                    result.and_then(|_| writeln!(f, "{}", field))
                })?;
                writeln!(f, "}}")
            }
            RegisterState { fields, pos } => {
                let (line, column) = pos.input_pos();
                let s = String::new();
                writeln!(f, "{:03}:{:03} | State(Registers) {{", line, column)?;
                fields.iter().fold(Ok(()), |result, field| {
                    result.and_then(|_| writeln!(f, "{}", field))
                })?;
                writeln!(f, "}}")
            }
            None => writeln!(f, "State(None)"),
        }
    }
}

/// Defines the software-visible interface of a unit
///
/// Similar to the state, there are multiple options of the interface:
///   - Memory: load/store to memory (normal DRAM)
///   - MMIORegisters: load/store to memory-mapped device registers
///   - CPURegisters: load/store to CPU registers
///   - SpecialRegisters: use of special instructions (no load/store) to those
#[derive(PartialEq, Clone)]
pub enum Interface {
    /// Defines a load/store interface to memory
    Memory { pos: SourcePos },
    /// Defines a memory-mapped interface to registers
    MMIORegisters { pos: SourcePos },
    /// Defines a load/store interface to CPU registers
    CPURegisters { pos: SourcePos },
    /// Defines a register interface using special instructions
    SpecialRegisters { pos: SourcePos },
    // TODO interface may be a combination: e.g., Memory + MMIORegisters
    //CombinedState {  },
    /// No software interface associated with this translation unit
    None,
}

/// Defines a Method inside a unit
///
/// A method defines certain functionality of the translation unit.
///
/// # Examples
///
///  - Translate(): a method that translates an address (required)
///  - get_size(): a method that extracts the
#[derive(PartialEq, Clone)]
pub struct Method {
    /// the name of the method
    pub name: String,
    /// the return type of the method
    pub rettype: Type,
    /// A list of arguments with their types
    pub args: Vec<(String, Type)>,
    /// A sequence of statements
    pub stmts: Vec<Stmt>,
    /// the position where the method was defined
    pub pos: SourcePos,
}

/// Implementation of the [fmt::Display] trait for [Field]
impl fmt::Display for Method {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "fn {}() -> {} {{", self.name, self.rettype)?;
        self.stmts.iter().fold(Ok(()), |result, s| {
            result.and_then(|_| writeln!(f, "  {}", s))
        })?;
        writeln!(f, "}}")
    }
}

/// Implementation of the [fmt::Debug] trait for [Field]
impl fmt::Debug for Method {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.pos.input_pos();
        writeln!(
            f,
            "{:03}:{:03} | fn {}() -> {} {{",
            line, column, self.name, self.rettype
        )?;
        self.stmts.iter().fold(Ok(()), |result, s| {
            result.and_then(|_| writeln!(f, "  {:?}", s))
        })?;
        writeln!(f, "}}")
    }
}

/// Defines an field in the state
///
/// A field may represent a 8, 16, 32, or 64 bit region in the state with a
/// specific bit layout.
#[derive(PartialEq, Clone)]
pub struct Field {
    /// the name of the field
    pub name: String,
    /// a reference to the state where the field is (base + offset)
    pub stateref: Option<(String, u64)>,
    /// the size of the field in bits
    pub length: u64,
    /// a vector of [BitSlice] representing the bitlayout
    pub layout: Vec<BitSlice>,
    /// the position where this field was defined
    pub pos: SourcePos,
}

/// Implementation of the [fmt::Display] trait for [Field]
impl fmt::Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.stateref {
            Some((s, o)) => writeln!(f, "{} [{}, {}, {}] {{", self.name, s, o, self.length)?,
            None => writeln!(f, "{} [{}] {{", self.name, self.length)?,
        };

        self.layout.iter().fold(Ok(()), |result, field| {
            result.and_then(|_| writeln!(f, "  {}", field))
        })?;
        writeln!(f, "}}")
    }
}

/// Implementation of the [fmt::Debug] trait for [Field]
impl fmt::Debug for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.pos.input_pos();
        write!(f, "{:03}:{:03} | ", line, column)?;
        match &self.stateref {
            Some((s, o)) => writeln!(f, "{} [{}, {}, {}] {{", self.name, s, o, self.length)?,
            None => writeln!(f, "{} [{}] {{", self.name, self.length)?,
        };

        self.layout.iter().fold(Ok(()), |result, field| {
            result.and_then(|_| writeln!(f, "  {:?}", field))
        })?;
        writeln!(f, "}}")
    }
}

/// Represents a bitslice of a [Field]
///
/// The field corresponds to the slice `[start..end]` of the [Field]
#[derive(PartialEq, Clone)]
pub struct BitSlice {
    /// the start bit
    pub start: u16,
    /// the end bit
    pub end: u16,
    /// the name of the slice
    pub name: String,
    /// where it was defined
    pub pos: SourcePos,
}

/// Implementation of the [fmt::Display] trait for [BitSlice]
impl fmt::Display for BitSlice {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[{:2}..{:2}]  {}", self.start, self.end, &self.name)
    }
}
/// Implementation of the [fmt::Debug] trait for [BitSlice]
impl fmt::Debug for BitSlice {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.pos.input_pos();
        write!(
            f,
            "{:03}:{:03} | [{:2}..{:2}]  {}",
            line, column, self.start, self.end, &self.name
        )
    }
}

/// Represents a statement
#[derive(Debug, PartialEq, Clone)]
pub enum Stmt {
    /// a block is a sequence of statements
    Block { stmts: Vec<Stmt>, pos: SourcePos },
    /// the assign statements gives a name to a value
    Assign {
        lhs: String,
        rhs: Expr,
        pos: SourcePos,
    },
    /// the conditional with
    IfElse {
        cond: Expr,
        then: Box<Stmt>,
        other: Option<Box<Stmt>>,
        pos: SourcePos,
    },
    /// assert statement
    Assert { expr: Expr, pos: SourcePos },
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Stmt::*;
        match self {
            Block { stmts, pos: _ } => {
                write!(f, "{{ TODO }} \n")
            }
            Assign { lhs, rhs, pos: _ } => write!(f, "let {} = {};\n", lhs, rhs),
            Assert { expr, pos: _ } => write!(f, "assert {};", expr),
            IfElse {
                cond,
                then,
                other,
                pos: _,
            } => match other {
                None => write!(f, "if {} {} \n", cond, then),
                Some(x) => write!(f, "if {} {} else {} \n", cond, then, x),
            },
        }
    }
}

/// Binary operations for [Expr] <OP> [Expr]
#[derive(Debug, PartialEq, Clone)]
pub enum BinOp {
    // arithmetic opreators
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
    // boolean operators
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
    // arithmetic operators
    Not,
    Ref,
    // boolean operator
    LNot,
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
            Identifier { path, pos: _ } => write!(format, "{}", path.join(".")),
            Number { value, pos: _ } => write!(format, "{}", value),
            Boolean { value, pos: _ } => write!(format, "{}", value),
            BinaryOperation {
                op,
                lhs,
                rhs,
                pos: _,
            } => write!(format, "({} {} {})", lhs, op, rhs),
            UnaryOperation { op, val, pos: _ } => write!(format, "{}({})", op, val),
            FnCall { path, pos: _ } => write!(format, "foo"),
            Slice {
                path,
                slice,
                pos: _,
            } => write!(format, "foo"),
        }
    }
}
