// Smt2 Code Generation - Function Declaration
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

//! Function Declaration

use std::fmt::{self, Display, Write};

use super::Formatter;

// a numeric literal <numeral>
// a decimal literal <decimal>
// a string literal <string>
// a binary literal <binary>
// a hex literal <hex>
// an <identifier>, which is one of:
// a symbol: <symbol>
// an indexed identifier: ( _ <symbol> <numeral>+ )
// a qualified-identifier: <identifier>
// or ( as <identifier> <sort>)
// a function application: ( <qualified-identifier> <expr>+)
// a forall-expression: ( forall ( (<symbol> <sort>)+ ) <expr>)
// an exists-expression: ( exists ( (<symbol> <sort>)+ ) <expr>)
// a let-expression: ( let ( (<symbol> <expr>)+ ) <expr>)
// an attributed expression: ( ! <expr> <attribute>+)

#[derive(Clone)]
pub struct LetBinding {
    var: String,
    val: Expr,
}

impl LetBinding {
    pub fn new(var: String, val: Expr) -> Self {
        Self { var, val }
    }

    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "({} ", self.var)?;
        self.val.fmt(fmt)?;
        write!(fmt, ")")
    }
}

/// Represents an expression in SMT2
///
/// # Example
///
/// ; expression
/// (+ a b)
///
#[derive(Clone)]
pub enum Expr {
    Numeral(u64),
    Decimal(f64),
    String(String),
    Binary(bool),
    // Hex(String),
    Identifier(String),
    // QualifiedIdentifier(String),
    FunctionApplication(String, Vec<Expr>),
    // Forall(Vec<LetBinding>, Box<Expr>),
    // Exists(Vec<LetBinding>, Box<Expr>),
    Let(Vec<LetBinding>, Box<Expr>),
    // AttributedExpr(Box<Expr>, Vec<Attribute>),
}

impl Expr {
    pub fn num(num: u64) -> Self {
        Expr::Numeral(num)
    }

    pub fn decimal(num: f64) -> Self {
        Expr::Decimal(num)
    }

    pub fn string(s: String) -> Self {
        Expr::String(s)
    }

    pub fn binary(b: bool) -> Self {
        Expr::Binary(b)
    }

    pub fn ident(s: String) -> Self {
        Expr::Identifier(s)
    }

    pub fn letexpr(vars: Vec<LetBinding>, expr: Expr) -> Self {
        Expr::Let(vars, Box::new(expr))
    }

    pub fn fn_apply(name: String, args: Vec<Expr>) -> Self {
        Expr::FunctionApplication(name, args)
    }

    pub fn eq(self, other: Expr) -> Expr {
        Expr::FunctionApplication("=".to_string(), vec![self, other])
    }

    pub fn implies(self, other: Expr) -> Expr {
        Expr::FunctionApplication("=>".to_string(), vec![self, other])
    }

    /// Formats the variant using the given formatter.
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Numeral(n) => write!(fmt, "{}", n),
            Expr::Decimal(n) => write!(fmt, "{}", n),
            Expr::String(s) => write!(fmt, "\"{}\"", s),
            Expr::Binary(b) => {
                if *b {
                    write!(fmt, "#b1")
                } else {
                    write!(fmt, "#b0")
                }
            }
            // Expr::Hex(s) => write!(fmt, "{}", s),
            Expr::Identifier(s) => write!(fmt, "{}", s),
            // Expr::QualifiedIdentifier(s) => write!(fmt, "{}", s),
            Expr::FunctionApplication(s, args) => {
                write!(fmt, "({} ", s)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(fmt, " ")?;
                    }
                    arg.fmt(fmt)?;
                }
                write!(fmt, ")")
            }
            // Expr::Forall(vars, expr) => {}
            // Expr::Exists(vars, expr) => {}
            Expr::Let(vars, expr) => {
                writeln!(fmt, "(let (")?;
                fmt.indent(|fmt| {
                    for var in vars.iter() {
                        var.fmt(fmt)?;
                        writeln!(fmt)?;
                    }
                    Ok(())
                })?;
                write!(fmt, ") ")?;
                expr.fmt(fmt)?;
                write!(fmt, ")")
            } // Expr::AttributedExpr(vars, expr) => {}
        }
    }
}
