// Velosiraptor Compiler
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

use std::fmt;

#[derive(Debug, PartialEq, Clone)]
pub struct Import {
    pub filename: String,
    pub pos: (u32, u32),
}

impl Import {
    pub fn new(filename: String, pos: (u32, u32)) -> Self {
        Import {
            filename,
            pos,
        }
    }
}

impl fmt::Display for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Import {}  ({}, {})",
            self.filename, self.pos.0, self.pos.1
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Unit {
    name: String,
    pos: (u32, u32),
}

impl Unit {
    pub fn new(name: String, pos: (u32, u32)) -> Self {
        Unit {
            name,
            pos,
        }
    }
}

impl fmt::Display for Unit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Unit {}  ({}, {})", self.name, self.pos.0, self.pos.1)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct File {
    filename: String,
    imports: Vec<Import>,
    units: Vec<Unit>,
}

impl File {
    pub fn new(filename: String, imports: Vec<Import>, units: Vec<Unit>) -> Self {
        File {
            filename,
            imports,
            units,
        }
    }
}

impl fmt::Display for File {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut imports = String::new();
        imports.push_str("  Imports:\n");
        for i in &self.imports {
            imports.push_str(&format!("    {}\n", i))
        }

        let mut units = String::new();
        units.push_str("  Units:");
        for u in &self.units {
            units.push_str(&format!("    {}\n", u))
        }

        write!(f, "File {}\n{}\n{}", self.filename, imports, units)
    }
}
