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

//mod constdef;

pub struct RosetteFile {
    /// the pathname of the file
    path: String,
    /// the document string
    doc: String,
    /// the language construct
    lang: String,
    /// the requres clauses
    requires: Vec<String>, // TODO: change me
    // the statemetns
    stmts: Vec<String>, // TODO: change me
}

/// implementation of the RosetteFile
impl RosetteFile {
    /// creates a new rosette file
    pub fn new(path: String, doc: String) -> Self {
        RosetteFile {
            path,
            doc,
            lang: String::from("rosette"),
            requires: Vec::new(),
            stmts: Vec::new(),
        }
    }

    /// adds a new requires clause to the file
    // pub fn add_new_requires(self, path: String) -> Self {
    //     let nreq = Requires::new();
    //     self.add_requires(self, nreq)
    // }

    /// adds a requires clause
    // pub fn add_requires(self, req: Requires) -> Self {
    //     self.requires.push(req);
    //     self
    // }

    /// adds a new struct definition to the file
    pub fn add_struct_def(self, id: String, entries: Vec<String>, attrib: String) -> Self {
        self
    }

    /// adds a type definition
    pub fn add_type_def(self) -> Self {
        self
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

    /// saves the rosette file
    pub fn save(&self) {}

    /// prints the content of the file to stdout
    pub fn print(&self) {}
}

pub trait RosetteFmt {
    fn fmt(self, indent: usize) -> String;
}
