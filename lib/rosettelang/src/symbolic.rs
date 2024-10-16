// Rosette Code Generation - Symbolic Variable Definitions
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

//! Symbolic Var Definitions

/// Represents a symbolic variable definition
///
/// # Example
///
/// ; the maximum depth
/// (define-symbolic va int64?)
///
pub struct SymbolicVar {
    /// the identifier of th e struct
    ident: String,
    /// the struct attributes
    ty: String,
    /// the optional size of the symbolic variable
    len: Option<usize>,
}

impl SymbolicVar {
    /// defines a new symbolic variable
    pub fn new(ident: String, ty: String, len: Option<usize>) -> Self {
        SymbolicVar { ident, ty, len }
    }

    /// formats corresponding rosette code
    pub fn to_code(&self) -> String {
        if let Some(l) = self.len {
            format!(
                "(define-symbolic {} {} #:length {})\n",
                self.ident, self.ty, l
            )
        } else {
            format!("(define-symbolic {} {})\n", self.ident, self.ty)
        }
    }
}
