// Velosiraptor ParseTree
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

//! Constant Ast Node
//!
//! This defines a constant node in the AST. The constant node represents a
//! defined constant either in the file or unit context

// the used standard library functionality
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter, Result};

// the used crate-internal functionality
use crate::ast::{
    utils, AstNode, AstNodeGeneric, Expr, Issues, Symbol, SymbolKind, SymbolTable, Type,
};
use crate::error::VrsError;
use crate::token::TokenStream;

/// Defines the value of the [Constant]
///
/// There are two types of constants: boolean and integer values.
/// Both can have either an expression or an integer value.
#[derive(PartialEq, Eq, Clone)]
pub enum ConstValue {
    IntegerValue(u64),
    IntegerExpr(Expr),
    BooleanValue(bool),
    BooleanExpr(Expr),
}

impl ConstValue {
    /// creates a new constant value with a boolean expression
    pub fn with_bool_expr(expr: Expr) -> Self {
        ConstValue::BooleanExpr(expr)
    }

    /// creates a new constant value with a integer expression
    pub fn with_int_expr(expr: Expr) -> Self {
        ConstValue::IntegerExpr(expr)
    }

    /// Return the type information of the constant value
    pub fn to_type(&self) -> Type {
        match self {
            ConstValue::IntegerValue(_) => Type::Integer,
            ConstValue::IntegerExpr(_) => Type::Integer,
            ConstValue::BooleanValue(_) => Type::Boolean,
            ConstValue::BooleanExpr(_) => Type::Boolean,
        }
    }

    // convers the value to an expression
    pub fn to_expr(&self, pos: TokenStream) -> Expr {
        match self {
            ConstValue::IntegerValue(v) => Expr::Number { value: *v, pos },
            ConstValue::IntegerExpr(e) => e.clone(),
            ConstValue::BooleanValue(v) => Expr::Boolean { value: *v, pos },
            ConstValue::BooleanExpr(e) => e.clone(),
        }
    }
}

/// implementation of the [fmt::Display] trait for the [ConstValue] enum
impl Display for ConstValue {
    fn fmt(&self, f: &mut Formatter) -> Result {
        use self::ConstValue::*;
        match self {
            IntegerValue(v) => write!(f, "{}", v),
            IntegerExpr(e) => write!(f, "{}", e),
            BooleanValue(v) => write!(f, "{}", v),
            BooleanExpr(e) => write!(f, "{}", e),
        }
    }
}

/// implementation of the [fmt::Debug] trait for the [ConstValue] enum
impl Debug for ConstValue {
    fn fmt(&self, f: &mut Formatter) -> Result {
        use self::ConstValue::*;
        match self {
            IntegerValue(v) => write!(f, "{}", v),
            IntegerExpr(e) => write!(f, "{}", e),
            BooleanValue(v) => write!(f, "{}", v),
            BooleanExpr(e) => write!(f, "{}", e),
        }
    }
}

/// implementation of [AstNodeGeneric] for [ConstValue]
impl<'a> AstNodeGeneric<'a> for ConstValue {
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        let mut res = Issues::ok();

        // Check 1: Expression is Valid
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: The expression value is consisting of valid symbols.
        // Notes:       --
        // --------------------------------------------------------------------------------------

        res = res
            + match self {
                ConstValue::IntegerExpr(e) => e.check(st),
                ConstValue::BooleanExpr(e) => e.check(st),
                _ => Issues::ok(),
            };

        // Check 2: Value is constant
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: The value assigned to the constant must be a constant expression.
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let (is_const, pos) = match self {
            ConstValue::IntegerExpr(e) => (e.is_const_expr(st), Some(e.loc())),
            ConstValue::BooleanExpr(e) => (e.is_const_expr(st), Some(e.loc())),
            _ => (true, None),
        };

        if !is_const {
            let msg = String::from("not a constant expression");
            let hint = String::from("convert the expression to a constant");
            VrsError::new_err(pos.unwrap(), msg, Some(hint)).print();
            res.inc_err(1);
        }

        res
    }

    fn name(&self) -> &str {
        "constant"
    }
}

/// Defines a [Constant] statement node
///
/// The constants statement defines and declares specific symbols
/// with constant values to be used throughout the definitions.
///
/// The constant can be defined as part of the file global definitions
/// or within a unit context.
///
/// A constant must have a valuet that can be calculated at compile time.
#[derive(PartialEq, Eq, Clone)]
pub struct Const {
    /// the identifier of the constant
    pub ident: String,
    /// the value the constant has
    pub value: ConstValue,
    /// position where the constant was defined in the source file
    pub pos: TokenStream,
}

impl Const {
    /// returns the expression that defines the value
    pub fn value(&self) -> &Expr {
        use ConstValue::*;
        match &self.value {
            IntegerValue(_v) => todo!("handle this!"),
            BooleanValue(_v) => todo!("handle this!"),
            BooleanExpr(e) => e,
            IntegerExpr(e) => e,
        }
    }

    /// creates a symbol from the current Const
    pub fn to_symbol(&self) -> Symbol {
        Symbol::new(
            String::from(self.name()),
            self.to_type(),
            SymbolKind::Const,
            self.loc().clone(),
            AstNode::Const(self),
        )
    }

    /// obtains the type of the constant
    pub fn to_type(&self) -> Type {
        self.value.to_type()
    }

    pub fn to_expr(&self) -> Expr {
        self.value.to_expr(self.pos.clone())
    }

    /// checks whether this constant is of integer type
    pub fn is_integer(&self) -> bool {
        self.value.to_type() == Type::Integer
    }

    /// checks whether this constant is of boolean type
    pub fn is_boolean(&self) -> bool {
        self.value.to_type() == Type::Boolean
    }
}

/// implementation of the [fmt::Display] trait for the [Const]
impl Display for Const {
    fn fmt(&self, f: &mut Formatter) -> Result {
        // TODO: make sure the type information is the right one!
        write!(
            f,
            "const {} : {}  = {};",
            self.ident,
            self.value.to_type(),
            self.value
        )
    }
}

/// implementation of the [fmt::Debug] trait for the [Const]
impl Debug for Const {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let (line, column) = self.pos.input_sourcepos().input_pos();
        write!(
            f,
            "{:03}:{:03} | const {} : {} = {:?};",
            line,
            column,
            self.ident,
            self.value.to_type(),
            self.value
        )
    }
}

/// implementation of [PartialOrd] for [Import]
impl PartialOrd for Const {
    /// This method returns an ordering between self and other values if one exists.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // we jus compare with the TokenStream position
        self.loc().partial_cmp(other.loc())
    }
}

/// implementation of [AstNodeGeneric] for [Const]
impl<'a> AstNodeGeneric<'a> for Const {
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        let mut res = Issues::ok();

        let name = self.name();
        let pos = self.loc();

        // Check 1: Expression is Valid
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: The expression value is consisting of valid symbols.
        // Notes:       --
        // --------------------------------------------------------------------------------------

        res = res + self.value.check(st);

        // Check 2: Identifier is ASCII
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: The name of the constant must be in ASCII characters.
        // Notes:       --
        // --------------------------------------------------------------------------------------

        if !name.is_ascii() {
            let msg = format!("constant `{}` should have an upper case name", name);
            let hint = format!(
                "convert the identifier to ASCII: `{}`",
                name.to_ascii_uppercase()
            );
            VrsError::new_err(pos.with_range(1..2), msg, Some(hint)).print();
            res.inc_err(1)
        }

        // Check 3:
        // --------------------------------------------------------------------------------------
        // Type:        Warning
        // Description: The name of the constant should be all upper-case
        // Notes:       --
        // --------------------------------------------------------------------------------------

        res + utils::check_upper_case(name, pos)
    }

    fn name(&self) -> &str {
        &self.ident
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        &self.pos
    }
}
