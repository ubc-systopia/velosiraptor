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

//! Smt2 Code Generation Library

use std::fmt;
use std::fmt::Write;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

// modules
mod datatype;
mod expr;
mod formatter;
mod function;
// mod functiondef;
// mod require;
// mod structdef;
// mod symbolic;
// mod vardef;

use formatter::Formatter;

// public re-exports
pub use datatype::DataType;
pub use expr::{Expr, LetBinding};
pub use function::Function;

// pub use crate::expr::{BVOp, RExpr};
// pub use crate::functiondef::FunctionDef;
// pub use crate::require::Require;
// pub use crate::structdef::StructDef;
// pub use crate::symbolic::SymbolicVar;
// pub use crate::vardef::VarDef;

/// defines a rosette expression
enum Smt2Stmt {
    DataType(DataType),
    // // a requires clause
    // Require(Require),
    // // structure definition
    // Struct(StructDef),
    // // a function/procedure definition
    Function(Function),
    // // a symbolic variable definition
    // Symbolic(SymbolicVar),
    // // a variable definition
    // Var(VarDef),
    // // a rosette expression
    // Expr(RExpr),

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
pub struct Smt2File {
    /// the pathname of the file
    path: PathBuf,
    /// the document string
    doc: String,
    // the statemetns
    stmts: Vec<Smt2Stmt>,
}

/// implementation of the Smt2File
impl Smt2File {
    /// creates a new rosette file
    pub fn new(path: PathBuf, doc: String) -> Self {
        Smt2File {
            path,
            doc,
            stmts: Vec::new(),
        }
    }

    /// adds a new section to the file
    pub fn add_section(&mut self, s: String) {
        self.stmts.push(Smt2Stmt::Section(s));
    }

    /// adds a new section to the file
    pub fn add_subsection(&mut self, s: String) {
        self.stmts.push(Smt2Stmt::SubSection(s));
    }

    /// adds a comment to the file
    pub fn add_comment(&mut self, comment: String) {
        self.stmts.push(Smt2Stmt::Comment(comment));
    }

    /// adds a comment to the file
    pub fn add_datatype(&mut self, datatype: DataType) {
        self.stmts.push(Smt2Stmt::DataType(datatype));
    }

    /// adds a new struct to the file
    pub fn add_new_function(
        &mut self,
        ident: String,
        rettype: String,
        args: Vec<String>,
        expr: Option<Expr>,
    ) {
        let mut f = Function::new(ident, rettype);
        if let Some(e) = expr {
            f.add_body(e);
        }
        self.add_function(f);
    }

    /// adds a function definition to the file
    pub fn add_function(&mut self, f: Function) {
        self.stmts.push(Smt2Stmt::Function(f));
    }

    pub fn add_const(&mut self, ident: String, ty: String, val: Expr) {
        let mut f = Function::new(ident, ty);
        f.add_body(val);
        self.add_function(f);
    }

    // /// defines a new symbolic variable
    // pub fn add_new_symbolic_var(&mut self, ident: String, ty: String) {
    //     let v = SymbolicVar::new(ident, ty, None);
    //     self.add_symbolic_var(v);
    // }

    // pub fn add_new_symbolic_var_list(&mut self, ident: String, ty: String, length: usize) {
    //     let v = SymbolicVar::new(ident, ty, Some(length));
    //     self.add_symbolic_var(v);
    // }

    // /// adds a symbolic variable to the file
    // pub fn add_symbolic_var(&mut self, v: SymbolicVar) {
    //     self.stmts.push(Smt2Stmt::Symbolic(v));
    // }

    // /// adds a new variable definition
    // pub fn add_new_var(&mut self, ident: String, ty: RExpr) {
    //     let v = VarDef::new(ident, ty);
    //     self.add_var(v);
    // }

    // /// adds a variable to the file
    // pub fn add_var(&mut self, v: VarDef) {
    //     self.stmts.push(Smt2Stmt::Var(v));
    // }

    // /// adds an expression  to the file
    // pub fn add_expr(&mut self, e: RExpr) {
    //     self.stmts.push(Smt2Stmt::Expr(e))
    // }

    // /// adds a type definition  to the file
    // pub fn add_type_def(&mut self) {}

    /// adds some raw code to the file
    pub fn add_raw(&mut self, code: String) {
        self.stmts.push(Smt2Stmt::Raw(code))
    }

    // formats the current context into smtlib2 syntax
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "; {}\n\n\n\n", self.doc)?;

        writeln!(fmt, "; preamble")?;

        writeln!(fmt, "(set-option :auto_config false)")?;
        writeln!(fmt, "(set-option :smt.mbqi false)")?;
        writeln!(fmt, "(set-option :smt.case_split 3)")?;
        writeln!(fmt, "(set-option :smt.qi.eager_threshold 100.0)")?;
        writeln!(fmt, "(set-option :smt.delay_units true)")?;
        writeln!(fmt, "(set-option :smt.arith.solver 2)")?;
        writeln!(fmt, "(set-option :smt.arith.nl false)")?;

        //write!(fmt, "(set-logic QF_BV)\n")?;

        for stmt in &self.stmts {
            use Smt2Stmt::*;
            match stmt {
                DataType(d) => d.fmt(fmt)?,
                Raw(s) => writeln!(fmt, "{}", s)?,
                Comment(s) => writeln!(fmt, "; {}", s)?,
                Section(s) => {
                    let sep = ";".repeat(100);
                    writeln!(fmt, "\n;{}\n; {}\n;{}\n", sep, s, sep)?;
                }
                SubSection(s) => {
                    let sep = "-".repeat(100);
                    writeln!(fmt, "\n; {}\n;{}", s, sep)?;
                }
                Function(f) => f.fmt(fmt)?,
            }
        }
        writeln!(fmt, "\n\n\n\n")?;
        writeln!(fmt, "(set-option :rlimit 150000000)")?;
        writeln!(fmt, "(check-sat)")?;
        writeln!(fmt, "(set-option :rlimit 0)")
    }

    /// formats the current file into rosette code
    pub fn to_code(&self) -> String {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret)).unwrap();
        ret
    }

    /// saves the rosette file
    pub fn save(&self) {
        // write the file, return IOError otherwise
        fs::write(&self.path, self.to_code()).expect("failed to execute process");

        // // grab the stdout
        // let s = match String::from_utf8(output.stdout) {
        //     Ok(v) => v,
        //     Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
        // };

        // // if it's empty, assume error
        // if s.is_empty() {
        //     let e = match String::from_utf8(output.stderr) {
        //         Ok(v) => v,
        //         Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
        //     };
        //     println!("rosette failure!");
        //     println!("{}", e);
        // }
        // // return the output caputured from stdout
        // // TODO: properly handle errors
        // s
    }
}

impl fmt::Display for Smt2File {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret))?;
        write!(f, "{}", ret)
    }
}
