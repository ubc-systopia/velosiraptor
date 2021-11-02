// Rosette Code Generation - Struct Definitions
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

//! Struct Definitions

// the formatter
use crate::RosetteFmt;

/// Represents a struct definition
///
/// # Example
///
/// ; defines the struct
/// (struct statefields (entry) #:transparent)
///
pub struct StructDef {
    /// the identifier of th e struct
    ident: String,
    /// the fields of the struct
    fields: Vec<String>,
    /// the struct attributes
    attrib: String,
    /// Comment
    doc: Option<String>,
}

/// implementation
impl StructDef {
    pub fn new(ident: String, fields: Vec<String>, attrib: String) -> Self {
        StructDef {
            ident,
            fields,
            attrib,
            doc: None,
        }
    }

    pub fn add_doc(&mut self, doc: String) {
        self.doc = Some(doc.replace("\n", ";\n"));
    }

    pub fn to_code(&self) -> String {
        let sdef = format!(
            "(struct {} ({}) {})\n",
            self.ident,
            self.fields.join(" "),
            self.attrib
        );
        if let Some(doc) = &self.doc {
            let mut structdef = format!("; {}\n", doc);
            structdef.push_str(sdef.as_str());
            return structdef;
        }
        sdef
    }
}

// impl RosetteFmt for TypeDef {
//     pub fn fmt(self, indent: usize) -> String {
//         let indent = (0..indent).map(|_| " ").collect::<String>();

//         let mut frags = Vec::new();

//         if let Some(doc) = self.doc {
//             frags.push(format!("; {}", doc))
//         }

//         frags.push(format!("(struct {} ({} {})"))

//         frags.push("; constructor")
//         frags.push("")

//     }
// }
