// Rosette Code Generation - Function Definitions
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

// the library includes
use crate::RExpr;

/// Represents a constante definition
///
/// # Example
///
/// ; the maximum depth
/// (define maxdepth 5)
///
pub struct FunctionDef {
    /// the identifier of th e struct
    ident: String,
    /// the function arguments
    args: Vec<String>,
    /// the expressions in the body
    exprs: Vec<RExpr>,
    /// the documentation
    doc: Option<String>,
    /// adds a suffix to the  define clause
    suffix: Option<String>,
}

impl FunctionDef {
    /// creates a new function definition
    pub fn new(ident: String, args: Vec<String>, exprs: Vec<RExpr>) -> Self {
        FunctionDef {
            ident,
            args,
            exprs,
            doc: None,
            suffix: None,
        }
    }

    /// adds a comment to the function
    pub fn add_comment(&mut self, comment: String) {
        self.doc = Some(comment.replace('\n', ";\n"));
    }

    /// adds a suffix to the define clause
    pub fn add_suffix(&mut self, suffix: String) {
        self.suffix = Some(suffix)
    }

    /// formats corresponding rosette code
    pub fn to_code(&self) -> String {
        let body = self
            .exprs
            .iter()
            .map(|e| e.to_code(2))
            .collect::<Vec<String>>();

        let suffix = match &self.suffix {
            Some(s) => format!("-{s}"),
            None => String::new(),
        };

        let f = format!(
            "(define{} ({} {})\n{}\n)\n",
            suffix,
            self.ident,
            self.args.join(" "),
            body.join("\n")
        );
        if let Some(c) = &self.doc {
            let mut doc = format!("; {c}\n");
            doc.push_str(f.as_str());
            return doc;
        }
        f
    }
}
