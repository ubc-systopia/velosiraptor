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
pub enum Ast {
    File {
        name: String,
        units: Box<Ast>,
        imports: Box<Ast>,
    },
    Import {
        filename: String,
        pos: (u32, u32),
    },
    Unit {
        name: String,
        pos: (u32, u32),
    },
    None,
}

impl Ast {
    pub fn import_from_sourcepos(ident: String, pos: (u32, u32)) -> Self {
        Ast::Import {
            filename: ident,
            pos: pos,
        }
    }
}

impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ast::File {
                name,
                units,
                imports,
            } => write!(
                f,
                "File {}\n  Imports:\n    {}\n  Units:\n     {}",
                name, units, imports
            ),
            Ast::Import {
                filename,
                pos: (l, c),
            } => write!(f, "Import {}  ({}, {})", filename, l, c),
            Ast::Unit { name, pos: (l, c) } => write!(f, "Unit {}  ({}, {})", name, l, c),
            Ast::None => write!(f, "None"),
        }
    }
}
