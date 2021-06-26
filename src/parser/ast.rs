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
        Import { filename, pos }
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
    pub name: String,
    pub pos: (u32, u32),
}

impl Unit {
    pub fn new(name: String, pos: (u32, u32)) -> Self {
        Unit { name, pos }
    }
}

impl fmt::Display for Unit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Unit {}  ({}, {})", self.name, self.pos.0, self.pos.1)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct File {
    pub filename: String,
    pub imports: Vec<Import>,
    pub units: Vec<Unit>,
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

#[derive(Debug, PartialEq, Clone)]
pub struct BitMapEntry {
    pub start: u16,
    pub end: u16,
    pub name: String,
    pub pos: (u32, u32),
}

impl BitMapEntry {
    pub fn new(start: u16, end: u16, name: String, pos: (u32, u32)) -> Self {
        BitMapEntry {
            start,
            end,
            name,
            pos,
        }
    }
}

impl fmt::Display for BitMapEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({:3}..{:3}, {})", self.start, self.end, &self.name)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct StateField {
    pub name: String,
    pub base: String,
    pub offset: u64,
    pub length: u64,
    pub bitmap: Vec<BitMapEntry>,
    pub pos: (u32, u32),
}

impl StateField {
    pub fn new(
        name: String,
        base: String,
        offset: u64,
        length: u64,
        bitmap: Vec<BitMapEntry>,
        pos: (u32, u32),
    ) -> Self {
        StateField {
            name,
            base,
            offset,
            length,
            bitmap,
            pos,
        }
    }
}

impl fmt::Display for StateField {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut entries = String::new();

        for b in &self.bitmap {
            entries.push_str(&format!("    {}\n", b))
        }

        write!(
            f,
            "    {} [{}, {}, {}] {{\n {}    }};\n",
            self.name, self.base, self.offset, self.length, entries
        )
    }
}

pub enum State {
    MemoryState {
        bases: Vec<String>,
        fields: Vec<StateField>,
        pos: (u32, u32),
    },
    RegisterState {
        bases: Vec<String>,
        fields: Vec<StateField>,
        pos: (u32, u32),
    },
    Dummy,
}
