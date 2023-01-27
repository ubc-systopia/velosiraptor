// Rosette Code Generation Library
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

//! Rosette Code Generation Library

use std::fs;
use std::path::PathBuf;
use std::process::Command;

// modules
mod expr;
mod functiondef;
mod require;
mod structdef;
mod symbolic;
mod vardef;

// public re-exports
pub use crate::expr::{BVOp, RExpr};
pub use crate::functiondef::FunctionDef;
pub use crate::require::Require;
pub use crate::structdef::StructDef;
pub use crate::symbolic::SymbolicVar;
pub use crate::vardef::VarDef;

/// defines a rosette expression
enum RosetteExpr {
    // a requires clause
    Require(Require),
    // structure definition
    Struct(StructDef),
    // a function/procedure definition
    Function(FunctionDef),
    // a symbolic variable definition
    Symbolic(SymbolicVar),
    // a variable definition
    Var(VarDef),
    // a rosette expression
    Expr(RExpr),
    // adds a section comment to the file
    Section(String),
    // adds a subsection comment to the file
    SubSection(String),
    // some normal comment
    Comment(String),
    // some raw rosette code
    Raw(String),
}

/// defines a rosette file
pub struct RosetteFile {
    /// the pathname of the file
    path: PathBuf,
    /// the document string
    doc: String,
    /// the language construct
    lang: String,
    // the statemetns
    exprs: Vec<RosetteExpr>, // TODO: change me
}

/// implementation of the RosetteFile
impl RosetteFile {
    /// creates a new rosette file
    pub fn new(path: PathBuf, doc: String) -> Self {
        RosetteFile {
            path,
            doc,
            lang: String::from("rosette"),
            exprs: Vec::new(),
        }
    }

    /// adds a new section to the file
    pub fn add_section(&mut self, s: String) {
        self.exprs.push(RosetteExpr::Section(s));
    }

    /// adds a new section to the file
    pub fn add_subsection(&mut self, s: String) {
        self.exprs.push(RosetteExpr::SubSection(s));
    }

    /// adds a comment to the file
    pub fn add_comment(&mut self, comment: String) {
        self.exprs.push(RosetteExpr::Comment(comment));
    }

    /// adds a new requires clause to the file
    pub fn add_new_require(&mut self, path: String) {
        let nreq = Require::new(path);
        self.add_require(nreq);
    }

    /// adds a requires clause to the file
    pub fn add_require(&mut self, req: Require) {
        self.exprs.push(RosetteExpr::Require(req))
    }

    /// adds a new struct to the file
    pub fn add_new_struct_def(&mut self, id: String, entries: Vec<String>, attrib: String) {
        let s = StructDef::new(id, entries, attrib);
        self.add_struct_def(s);
    }

    /// adds a struct to the file
    pub fn add_struct_def(&mut self, s: StructDef) {
        self.exprs.push(RosetteExpr::Struct(s));
    }

    /// adds a new struct to the file
    pub fn add_new_function_def(&mut self, ident: String, args: Vec<String>, exprs: Vec<RExpr>) {
        let f = FunctionDef::new(ident, args, exprs);
        self.add_function_def(f);
    }

    /// adds a function definition to the file
    pub fn add_function_def(&mut self, f: FunctionDef) {
        self.exprs.push(RosetteExpr::Function(f));
    }

    /// defines a new symbolic variable
    pub fn add_new_symbolic_var(&mut self, ident: String, ty: String) {
        let v = SymbolicVar::new(ident, ty, None);
        self.add_symbolic_var(v);
    }

    pub fn add_new_symbolic_var_list(&mut self, ident: String, ty: String, length: usize) {
        let v = SymbolicVar::new(ident, ty, Some(length));
        self.add_symbolic_var(v);
    }

    /// adds a symbolic variable to the file
    pub fn add_symbolic_var(&mut self, v: SymbolicVar) {
        self.exprs.push(RosetteExpr::Symbolic(v));
    }

    /// adds a new variable definition
    pub fn add_new_var(&mut self, ident: String, ty: RExpr) {
        let v = VarDef::new(ident, ty);
        self.add_var(v);
    }

    /// adds a variable to the file
    pub fn add_var(&mut self, v: VarDef) {
        self.exprs.push(RosetteExpr::Var(v));
    }

    /// adds an expression  to the file
    pub fn add_expr(&mut self, e: RExpr) {
        self.exprs.push(RosetteExpr::Expr(e))
    }

    /// adds a type definition  to the file
    pub fn add_type_def(&mut self) {}

    /// adds some raw code to the file
    pub fn add_raw(&mut self, code: String) {
        self.exprs.push(RosetteExpr::Raw(code))
    }

    /// formats the current file into rosette code
    pub fn to_code(&self) -> String {
        let mut s = format!("; {}\n\n#lang {}\n\n", self.doc, self.lang);

        for expr in &self.exprs {
            use RosetteExpr::*;
            let code = match expr {
                Require(r) => r.to_code(),
                Struct(s) => s.to_code(),
                Symbolic(v) => v.to_code(),
                Var(v) => v.to_code(),
                Expr(e) => e.to_code(0),
                Raw(s) => s.clone(),
                Function(f) => format!("\n{}", f.to_code()),
                Comment(s) => format!("; {s}\n"),
                Section(s) => {
                    let sep = ";".repeat(80);
                    format!("\n;{sep}\n; {s}\n;{sep}\n\n")
                }
                SubSection(s) => {
                    let sep = "-".repeat(80);
                    format!("\n; {s}\n;{sep}\n")
                }
            };
            s.push_str(code.as_str());
        }
        s
    }

    /// saves the rosette file
    pub fn save(&self) {
        // write the file, return IOError otherwise
        fs::write(&self.path, self.to_code().as_bytes()).expect("failed to execute process");
    }

    /// prints the content of the file to stdout
    pub fn print(&self) {}

    /// invokes racket with the rosette file
    pub fn exec(&mut self) -> String {
        // just call racket, requires it to be part of the search path
        let output = Command::new("racket")
            .args([&self.path])
            .output()
            .expect("failed to execute process");

        // grab the stdout
        let s = match String::from_utf8(output.stdout) {
            Ok(v) => v,
            Err(e) => panic!("Invalid UTF-8 sequence: {e}"),
        };

        // if it's empty, assume error
        if s.is_empty() {
            let e = match String::from_utf8(output.stderr) {
                Ok(v) => v,
                Err(e) => panic!("Invalid UTF-8 sequence: {e}"),
            };
            println!("rosette failure!");
            println!("{e}");
        }
        // return the output caputured from stdout
        // TODO: properly handle errors
        s
    }
}
