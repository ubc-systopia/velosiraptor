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

//mod constdef;
mod require;

use crate::require::Require;

pub struct RosetteFile {
    /// the pathname of the file
    path: PathBuf,
    /// the document string
    doc: String,
    /// the language construct
    lang: String,
    /// the requres clauses
    requires: Vec<Require>, // TODO: change me
    // the statemetns
    stmts: Vec<String>, // TODO: change me
}

/// implementation of the RosetteFile
impl RosetteFile {
    /// creates a new rosette file
    pub fn new(path: PathBuf, doc: String) -> Self {
        RosetteFile {
            path,
            doc,
            lang: String::from("rosette"),
            requires: Vec::new(),
            stmts: Vec::new(),
        }
    }

    /// adds a new requires clause to the file
    pub fn add_new_require(&mut self, path: String) {
        let nreq = Require::new(path);
        self.add_require(nreq);
    }

    /// adds a requires clause
    pub fn add_require(&mut self, req: Require) {
        self.requires.push(req);
    }

    /// adds a new struct definition to the file
    pub fn add_struct_def(&mut self, id: String, entries: Vec<String>, attrib: String) {}

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

        for r in &self.requires {
            let code = r.to_code();
            s.push_str(code.as_str());
        }
        s
    }

    /// saves the rosette file
    pub fn save(&self) {
        // write the file, return IOError otherwise
        fs::write(&self.path, self.to_code().as_bytes());
    }

    /// prints the content of the file to stdout
    pub fn print(&self) {}

    ///
    pub fn synth(&self) {}
}

pub trait RosetteFmt {
    fn fmt(self, indent: usize) -> String;
}
