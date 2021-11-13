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

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alphanumeric1, digit1, hex_digit1, newline, space0, space1},
    combinator::{all_consuming, opt, recognize},
    multi::many1,
    sequence::{delimited, preceded, terminated, tuple},
    Err, IResult,
};

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
    Raw(String),
}

#[derive(Debug)]
pub enum OpArg {
    Num(u64),
    Var(String),
    None,
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

    pub fn add_raw(&mut self, code: String) {
        self.exprs.push(RosetteExpr::Raw(code))
    }

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
                Raw(s) => s.clone(),
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

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Result Parsing
    ///////////////////////////////////////////////////////////////////////////////////////////////

    /// parser to recognize a bitvector constaint `(bv #x1 64)`
    fn parse_oparg_bv(s: &str) -> IResult<&str, OpArg> {
        let bv = tuple((tag("(bv"), space1));
        let width = tuple((space1, digit1, tag(")")));
        let value = preceded(tag("#x"), hex_digit1);

        let (r, n) = delimited(bv, value, width)(s)?;
        match u64::from_str_radix(n, 16) {
            Ok(i) => Ok((r, OpArg::Num(i))),
            Err(_) => panic!("number {} not parsable as hex", n),
        }
    }

    /// parser to recognize a sybolic variable `pa`
    fn parse_oparg_var(s: &str) -> IResult<&str, OpArg> {
        let (r, n) = alphanumeric1(s)?;
        Ok((r, OpArg::Var(String::from(n))))
    }

    /// parser to recognize a single operation `(op arg)`
    fn parse_op(s: &str) -> IResult<&str, (String, OpArg)> {
        // the op name is alphanumeric + '_'
        let opname = recognize(many1(alt((alphanumeric1, tag("_")))));
        // the opargs are bv, var, or nothing

        let opargs = opt(alt((Self::parse_oparg_bv, Self::parse_oparg_var)));
        // the operation is then the name, followed by maybe arguments

        let op = tuple((opname, preceded(space0, opargs)));
        // the operation is delimted in parenthesis

        let (r, (n, a)) = delimited(tag("("), op, tag(")"))(s)?;
        // get the argumetn, or set it to None if there was none

        let arg = a.unwrap_or(OpArg::None);
        Ok((r, (String::from(n), arg)))
    }

    /// parser to recognize a sequence `(Seq Op [Seq | Res])`
    fn parse_seq(s: &str) -> IResult<&str, Vec<(String, OpArg)>> {
        let next = preceded(space1, alt((Self::parse_seq, Self::parse_res)));
        let (s1, op) = preceded(tag("(Seq "), Self::parse_op)(s)?;
        let (s2, rops) = terminated(next, tag(")"))(s1)?;

        let mut ops = vec![op];
        ops.extend(rops);
        Ok((s2, ops))
    }

    /// parser to recognize the return statement `(Return)`
    fn parse_res(s: &str) -> IResult<&str, Vec<(String, OpArg)>> {
        println!("parse_res: {}", s);
        let (r, _) = delimited(tag("("), tag("Return"), tag(")"))(s)?;
        Ok((r, vec![(String::from("return"), OpArg::None)]))
    }

    /// parse and validate the result from Rosette
    fn parse_result(output: &str) {
        let ops = match all_consuming(terminated(Self::parse_seq, newline))(output) {
            Ok((_, v)) => v,
            Err(e) => panic!("parser did not finish: {:?}", e),
        };
        for o in ops {
            println!("OP: {:?} {:?}", o.0, o.1)
        }
    }

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
        Self::parse_result(s.as_str());

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

#[test]
fn test_parser() {
    let s = "(Seq (Op_Iface_sz_bytes_Insert (bv #x4000000000000000 64)) (Seq (Op_Iface_sz_WriteAction) (Seq (Op_Iface_flags_present_Insert (bv #x0000000000000001 64)) (Seq (Op_Iface_flags_WriteAction) (Seq (Op_Iface_address_base_Insert pa) (Seq (Op_Iface_address_WriteAction) (Return)))))))";
    RosetteFile::parse_result(s);
}
