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

//mod constdef;
mod expr;
mod functiondef;
mod require;
mod structdef;
mod symbolic;
mod typedef;
mod vardef;

pub use crate::expr::{BVOp, RExpr};
pub use crate::functiondef::FunctionDef;
pub use crate::require::Require;
pub use crate::structdef::StructDef;
pub use crate::symbolic::SymbolicVar;
pub use crate::vardef::VarDef;

enum RosetteExpr {
    Require(Require),
    Struct(StructDef),
    Comment(String),
    Function(FunctionDef),
    Symbolic(SymbolicVar),
    Var(VarDef),
    Expr(RExpr),
    Section(String),
    SubSection(String),
}

const SECTION_SEP: &str =
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;";
const SUBSECTION_SEP: &str =
    "------------------------------------------------------------------------------";

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

    /// adds a new requires clause to the file
    pub fn add_new_require(&mut self, path: String) {
        let nreq = Require::new(path);
        self.add_require(nreq);
    }

    /// adds a requires clause
    pub fn add_require(&mut self, req: Require) {
        self.exprs.push(RosetteExpr::Require(req))
    }

    /// adds a comment to the file
    pub fn add_comment(&mut self, comment: String) {
        self.exprs.push(RosetteExpr::Comment(comment));
    }

    /// adds a new section to the file
    pub fn add_section(&mut self, s: String) {
        self.exprs.push(RosetteExpr::Section(s));
    }

    /// adds a new section to the file
    pub fn add_subsection(&mut self, s: String) {
        self.exprs.push(RosetteExpr::SubSection(s));
    }

    /// adds a new struct to the file
    pub fn add_new_struct_def(&mut self, id: String, entries: Vec<String>, attrib: String) {
        let s = StructDef::new(id, entries, attrib);
        self.add_struct_def(s);
    }

    /// adds a struct to the curren tfile
    pub fn add_struct_def(&mut self, s: StructDef) {
        self.exprs.push(RosetteExpr::Struct(s));
    }

    /// adds a new struct to the file
    pub fn add_new_function_def(&mut self, ident: String, args: Vec<String>, exprs: Vec<RExpr>) {
        let f = FunctionDef::new(ident, args, exprs);
        self.add_function_def(f);
    }

    /// adds a struct to the curren tfile
    pub fn add_function_def(&mut self, f: FunctionDef) {
        self.exprs.push(RosetteExpr::Function(f));
    }

    ///
    pub fn add_new_symbolic_var(&mut self, ident: String, ty: String) {
        let v = SymbolicVar::new(ident, ty);
        self.add_symbolic_var(v);
    }

    pub fn add_symbolic_var(&mut self, v: SymbolicVar) {
        self.exprs.push(RosetteExpr::Symbolic(v));
    }

    pub fn add_new_var(&mut self, ident: String, ty: RExpr) {
        let v = VarDef::new(ident, ty);
        self.add_var(v);
    }

    pub fn add_var(&mut self, v: VarDef) {
        self.exprs.push(RosetteExpr::Var(v));
    }

    pub fn add_expr(&mut self, e: RExpr) {
        self.exprs.push(RosetteExpr::Expr(e))
    }

    /// adds a type definition
    pub fn add_type_def(&mut self) {}

    /// adds a new statement to the file
    // pub fn add_stmt(self, nstmt: Stmt) -> Self {
    //     self.stmts.push(nstmt)
    //     self
    // }

    /// adds a new section to the file
    ///
    /// a section is basically a comment that acts as a visual divisor
    ///
    // pub fn add_section(self, sec: String) -> Self {
    //     let nstmt = sec
    //     self.add_stmt(nstmt)
    // }

    /// adds a new sub section to the file
    ///
    /// a subsection is basically a comment that acts as a visual divisor
    ///
    // pub fn add_subsection(self, sec: String) -> Self {
    //     let nstmt = sec
    //     self.add_stmt(nstmt)
    // }

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
                Function(f) => format!("\n{}", f.to_code()),
                Comment(s) => format!("; {}\n", s),
                Section(s) => format!("\n;{}\n; {}\n;{}\n\n", SECTION_SEP, s, SECTION_SEP),
                SubSection(s) => format!("\n; {}\n;{}\n", s, SUBSECTION_SEP),
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

    ///

    pub fn synth(&self) {
        let output = Command::new("/home/achreto/bin/racket/bin/racket")
            .args([&self.path])
            .output()
            .expect("failed to execute process");

        let s = match String::from_utf8(output.stdout) {
            Ok(v) => v,
            Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
        };

        println!("SYNTH RESULT:");
        println!("{}", s);

        let s = match String::from_utf8(output.stderr) {
            Ok(v) => v,
            Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
        };

        println!("{}", s);
        println!("SYNTH RESULT END.");
    }
}

pub trait RosetteFmt {
    fn fmt(self, indent: usize) -> String;
}
