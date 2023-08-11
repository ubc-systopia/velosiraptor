// Velosiraptor Ast
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! Operations
//!
//! This module defines a set of possible operations that can occur in the
//! map/unmap/protect operations.

use std::rc::Rc;

/// Represents an operation expression such as `a + b`
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiOpExpr {
    /// a constant number
    Num(u64),
    /// a variable
    Var(String),
    /// shift left
    Shl(Box<VelosiOpExpr>, Box<VelosiOpExpr>),
    /// logic shift right
    Shr(Box<VelosiOpExpr>, Box<VelosiOpExpr>),
    /// addition
    Add(Box<VelosiOpExpr>, Box<VelosiOpExpr>),
    /// subtraction
    Sub(Box<VelosiOpExpr>, Box<VelosiOpExpr>),
    /// bitwise and
    And(Box<VelosiOpExpr>, Box<VelosiOpExpr>),
    /// bitwise or
    Or(Box<VelosiOpExpr>, Box<VelosiOpExpr>),
    /// multiplication
    Mul(Box<VelosiOpExpr>, Box<VelosiOpExpr>),
    /// division
    Div(Box<VelosiOpExpr>, Box<VelosiOpExpr>),
    /// modulus
    Mod(Box<VelosiOpExpr>, Box<VelosiOpExpr>),
    /// not
    Not(Box<VelosiOpExpr>),
    /// extracts the flags from the variable
    Flags(String, String),
    /// no expression
    None,
}

/// represents an operation
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiOperation {
    InsertSlice(Rc<String>, Rc<String>, VelosiOpExpr),
    ExtractSlice(Rc<String>, Rc<String>),
    InsertField(Rc<String>, VelosiOpExpr),
    WriteAction(Rc<String>),
    ReadAction(Rc<String>),
    GlobalBarrier,
    Return,
}

impl VelosiOperation {
    pub fn fieldname(&self) -> &str {
        match self {
            VelosiOperation::InsertSlice(s, _, _) => s,
            VelosiOperation::InsertField(s, _) => s,
            VelosiOperation::ExtractSlice(s, _) => s,
            VelosiOperation::WriteAction(s) => s,
            VelosiOperation::ReadAction(s) => s,
            VelosiOperation::GlobalBarrier => "",
            VelosiOperation::Return => "",
        }
    }
}
