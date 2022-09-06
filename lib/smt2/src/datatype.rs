// Smt2 Code Generation - Datatype Declaration
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

//! Datatype Declaration

use std::fmt::{self, Display, Write};

use super::Formatter;

struct DatatTypeField {
    name: String,
    ty: String,
}

impl DatatTypeField {
    fn new(name: String, ty: String) -> Self {
        DatatTypeField { name, ty }
    }

    /// Formats the variant using the given formatter.
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "({} {})", self.name, self.ty)
    }
}

impl Display for DatatTypeField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret)).unwrap();
        write!(f, "{}", ret)
    }
}

/// Represents a datatype declaration in SMT2
///
/// # Example
///
/// ; data type
/// (declare-datatypes ((State 0))) ((State/State (State/State/Field Int)))
///
pub struct DataType {
    /// the name of the datatype
    name: String,
    /// the number of type parameters
    arty: u8,
    /// the fields of the datatype
    fields: Vec<DatatTypeField>,
    /// a comment string for the requires clause
    comment: Option<String>,
}

impl DataType {
    /// creates a new requires expression
    pub fn new(name: String, arty: u8) -> Self {
        DataType {
            name,
            arty,
            fields: Vec::new(),
            comment: None,
        }
    }

    /// adds a comment to the requires expression
    pub fn add_comment(&mut self, comment: String) -> &mut Self {
        self.comment = Some(comment.replace('\n', ";\n"));
        self
    }

    /// adds a field to the datatype
    pub fn add_field(&mut self, name: String, ty: String) -> &mut Self {
        self.fields.push(DatatTypeField::new(name, ty));
        self
    }

    /// Formats the variant using the given formatter.
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        if let Some(c) = &self.comment {
            writeln!(fmt, ";; {}", c)?;
        }

        writeln!(
            fmt,
            "(declare-datatypes (({}_t {})) (",
            self.name, self.arty
        )?;

        // (State./State (State./State/?pte StatePte.) (State./State/?pte2 Int))

        fmt.indent(|fmt| {
            write!(fmt, "(({} ", self.name)?;
            for (i, f) in self.fields.iter().enumerate() {
                if i > 0 {
                    write!(fmt, " ")?;
                }
                f.fmt(fmt)?;
            }
            write!(fmt, "))")
        })?;
        writeln!(fmt, "))")?;

        // the constructors
        writeln!(fmt, "\n;; constructor for {} fields", self.name)?;

        // the accessors
        writeln!(fmt, "\n;; accessors for {} fields\n", self.name)?;

        for f in self.fields.iter() {
            // (declare-fun State.pte.val (State.) Int)
            writeln!(
                fmt,
                "(declare-fun {}.get ({}_t) {})",
                f.name, self.name, f.ty
            )?;
            writeln!(
                fmt,
                "(declare-fun {}.set ({}_t {}) {}_t)",
                f.name, self.name, f.ty, self.name
            )?;
            writeln!(fmt)?;
        }

        for (i, f) in self.fields.iter().enumerate() {
            // (declare-fun State.pte.val (State.) Int)
            writeln!(
                fmt,
                ";; (declare-fun {}.get ({}_t) {})",
                f.name, self.name, f.ty
            )?;
            writeln!(
                fmt,
                "(assert (forall ((x@ {}_t)) (= ({}.get x@) ({} x@))))",
                self.name, f.name, f.name
            )?;
            writeln!(
                fmt,
                ";; (declare-fun {}.set ({}_t {}) {}_t)",
                f.name, self.name, f.ty, self.name
            )?;
            write!(
                fmt,
                "(assert (forall ((x@ {}_t) (v@ {})) (= ({}.set x@ v@) ({} ",
                self.name, f.ty, f.name, self.name
            )?;
            for (j, f2) in self.fields.iter().enumerate() {
                if i == j {
                    write!(fmt, "v@ ")?;
                } else {
                    write!(fmt, "({}.get x@) ", f2.name)?;
                }
            }

            writeln!(fmt, "))))\n")?;
        }

        // (assert
        //     (forall ((x@ StatePte.)) (!
        //       (= (StatePte./StatePte/_0 x@) (StatePte./StatePte/?_0 x@))
        //       :pattern ((StatePte./StatePte/_0 x@))
        //       :qid
        //       internal_StatePte./StatePte/_0_accessor_definition
        //       :skolemid
        //       skolem_internal_StatePte./StatePte/_0_accessor_definition
        //    )))

        Ok(())
    }
}

impl Display for DataType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret)).unwrap();
        write!(f, "{}", ret)
    }
}
