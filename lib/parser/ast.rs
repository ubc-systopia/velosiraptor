// Velosiraptor Parser
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

pub struct Ast {}

use crate::lexer::sourcepos::SourcePos;

///
/// Defines an import statement
///
#[derive(Debug, PartialEq, Clone)]
pub struct Import<'a> {
    pub name: String,
    pub pos: SourcePos<'a>,
}

impl<'a> Import<'a> {
    pub fn new(name: String, pos: SourcePos<'a>) -> Self {
        Import { name, pos }
    }
}

impl<'a> fmt::Display for Import<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Import {}  ({:?})", self.name, self.pos.get_pos())
    }
}

///
/// Defines a translation unit
///
#[derive(Debug, PartialEq, Clone)]
pub struct Unit<'a> {
    pub name: String,
    pub derived: Option<String>,
    pub pos: SourcePos<'a>,
}

impl<'a> Unit<'a> {
    pub fn new(name: String, derived: Option<String>, pos: SourcePos<'a>) -> Self {
        Unit { name, derived, pos }
    }
}

impl<'a> fmt::Display for Unit<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.derived {
            Some(n) => write!(f, "Unit {} : {}  ({:?})", self.name, n, self.pos.get_pos()),
            None => write!(f, "Unit {}  ({:?})", self.name, self.pos.get_pos()),
        }
    }
}

// #[derive(Debug, PartialEq, Clone)]
// pub struct File {
//     pub filename: String,
//     pub imports: Vec<Import>,
//     pub units: Vec<Unit>,
// }

// impl File {
//     pub fn new(filename: String, imports: Vec<Import>, units: Vec<Unit>) -> Self {
//         File {
//             filename,
//             imports,
//             units,
//         }
//     }
// }

// impl fmt::Display for File {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         let mut imports = String::new();
//         imports.push_str("  Imports:\n");
//         for i in &self.imports {
//             imports.push_str(&format!("    {}\n", i))
//         }

//         let mut units = String::new();
//         units.push_str("  Units:");
//         for u in &self.units {
//             units.push_str(&format!("    {}\n", u))
//         }

//         write!(f, "File {}\n{}\n{}", self.filename, imports, units)
//     }
// }

#[derive(Debug, PartialEq, Clone)]
pub struct BitSlice<'a> {
    pub start: u16,
    pub end: u16,
    pub name: String,
    pub pos: SourcePos<'a>,
}

impl<'a> BitSlice<'a> {
    pub fn new(start: u16, end: u16, name: String, pos: SourcePos<'a>) -> Self {
        BitSlice {
            start,
            end,
            name,
            pos,
        }
    }
}

impl<'a> fmt::Display for BitSlice<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({:3}..{:3}, {})", self.start, self.end, &self.name)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Field<'a> {
    pub name: String,
    pub base: String,
    pub offset: u64,
    pub length: u64,
    pub slices: Vec<BitSlice<'a>>,
    pub pos: SourcePos<'a>,
}

impl<'a> Field<'a> {
    pub fn new(
        name: String,
        base: String,
        offset: u64,
        length: u64,
        slices: Vec<BitSlice<'a>>,
        pos: SourcePos<'a>,
    ) -> Self {
        Field {
            name,
            base,
            offset,
            length,
            slices,
            pos,
        }
    }
}

impl<'a> fmt::Display for Field<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut entries = String::new();

        for b in &self.slices {
            entries.push_str(&format!("    {}\n", b))
        }

        write!(
            f,
            "    {} [{}, {}, {}] {{\n {}    }};\n",
            self.name, self.base, self.offset, self.length, entries
        )
    }
}

// pub enum State {
//     MemoryState {
//         bases: Vec<String>,
//         fields: Vec<StateField>,
//         pos: (u32, u32),
//     },
//     RegisterState {
//         bases: Vec<String>,
//         fields: Vec<StateField>,
//         pos: (u32, u32),
//     },
//     Dummy,
// }
