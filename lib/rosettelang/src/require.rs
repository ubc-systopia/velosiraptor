// Rosette Code Generation - Requires Clauses
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

//! Require Clause

/// Represents a 'require' clause in rosette
///
/// # Example
///
/// ; include the syntax module
/// (require rosette/lib/synthax)
///
pub struct Require {
    /// the path of the module to be included (e.g., rosette/lib/syntax)
    path: String,
    /// a comment string for the requires clause
    comment: Option<String>,
}

impl Require {
    /// creates a new requires expression
    pub fn new(path: String) -> Self {
        Require {
            path,
            comment: None,
        }
    }

    // adds a comment to the requires expression
    pub fn add_comment(&mut self, comment: String) {
        self.comment = Some(comment.replace("\n", ";\n"));
    }

    /// formats the requires block into code
    pub fn to_code(&self) -> String {
        let req = format!("(require {})\n", self.path);
        if let Some(c) = &self.comment {
            let mut comment = format!("; {}", c);
            comment.push_str(req.as_str());
            return comment;
        }
        req
    }
}
