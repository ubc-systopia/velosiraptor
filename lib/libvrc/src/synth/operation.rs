// Velosiraptor Code Generator
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

//! Operations

#[derive(PartialEq, Clone, Debug)]
pub enum OpExpr {
    /// a constant number
    Num(u64),
    /// a variable
    Var(String),
    Shl(Box<OpExpr>, Box<OpExpr>),
    Shr(Box<OpExpr>, Box<OpExpr>),
    Add(Box<OpExpr>, Box<OpExpr>),
    Sub(Box<OpExpr>, Box<OpExpr>),
    And(Box<OpExpr>, Box<OpExpr>),
    Or(Box<OpExpr>, Box<OpExpr>),
    Mul(Box<OpExpr>, Box<OpExpr>),
    Div(Box<OpExpr>, Box<OpExpr>),
    Mod(Box<OpExpr>, Box<OpExpr>),
    None,
}

#[derive(PartialEq, Clone, Debug)]
pub enum Operation {
    Insert {
        field: String,
        slice: Option<String>,
        arg: OpExpr,
    },
    Extract {
        field: String,
        slice: Option<String>,
    },
    WriteAction {
        field: String,
    },
    ReadAction {
        field: String,
    },
    Return,
}

impl Operation {
    pub fn insert(field: &str, slice: Option<&str>, op: OpExpr) -> Self {
        Operation::Insert {
            field: field.to_string(),
            slice: slice.map(|s| s.to_string()),
            arg: op,
        }
    }
    pub fn extract(field: &str, slice: Option<&str>) -> Self {
        Operation::Extract {
            field: field.to_string(),
            slice: slice.map(|s| s.to_string()),
        }
    }
    pub fn write(field: &str) -> Self {
        Operation::WriteAction {
            field: field.to_string(),
        }
    }
    pub fn read(field: &str) -> Self {
        Operation::ReadAction {
            field: field.to_string(),
        }
    }
    pub fn ret() -> Self {
        Operation::Return
    }

    pub fn fieldname(&self) -> &str {
        match self {
            Operation::Insert { field, .. } => field,
            Operation::Extract { field, .. } => field,
            Operation::WriteAction { field, .. } => field,
            Operation::ReadAction { field, .. } => field,
            Operation::Return => "",
        }
    }
}
