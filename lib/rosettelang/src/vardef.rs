// Rosette Code Generation - Const Definitions
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

//! Const Definitions

use crate::expr::RExpr;

/// Represents a constante definition
///
/// # Example
///
/// ; the maximum depth
/// (define maxdepth 5)
///
pub struct VarDef {
    /// the identifier of th e struct
    ident: String,
    /// the struct attributes
    value: RExpr,
}

/// implementation
impl VarDef {
    pub fn new(ident: String, value: RExpr) -> Self {
        VarDef { ident, value }
    }

    pub fn to_code(&self) -> String {
        format!("(define {} \n{}\n)", self.ident, self.value.to_code(2))
    }
}
