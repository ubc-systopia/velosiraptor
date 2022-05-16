// Velosiraptor ParseTree
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

//! Ast representation of the VelosiRaptor Definitions

use std::fmt;

/// represents the known types.
///
/// The type of a an expression, parameter or value defines the set of
/// operations that are allowed to be carried out with it.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Type {
    /// a boolean type (true / false)
    Boolean,
    /// An integer type
    Integer,
    /// Represents an address value
    Address,
    /// The size defines the number of addresses within a range
    Size,
    /// the state of a unit
    State,
    /// the interface of a unit
    Interface,
    /// represents the the unit
    Unit,
    /// the flags of a unit
    Flags,
}

/// Implementation for [Type]
impl Type {
    /// returns true if the type is numeric
    pub fn is_numeric(&self) -> bool {
        use Type::*;
        match self {
            Boolean => false,
            Integer => true,
            Address => true,
            Size => true,
            Flags => true,
            State => false,
            Interface => false,
            Unit => false,
        }
    }

    /// returns true iff the type is boolean
    pub fn is_boolean(&self) -> bool {
        use Type::*;
        match self {
            Boolean => true,
            Integer => false,
            Address => false,
            Flags => false,
            Size => false,
            State => false,
            Interface => false,
            Unit => false,
        }
    }

    /// returns true iff the type is boolean
    pub fn to_type_string(&self) -> &str {
        use Type::*;
        match self {
            Boolean => "boolean",
            Integer => "numeric",
            Address => "numeric",
            Flags => "flags",
            Size => "numeric",
            State => "state",
            Interface => "interface",
            Unit => "unit",
        }
    }

    /// returns true if two types are compatible
    pub fn compatible(&self, other: Self) -> bool {
        self.is_boolean() && other.is_boolean() || self.is_numeric() && other.is_numeric()
    }
}

/// implementation of the [fmt::Display] trait for the [Type].
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Type::*;
        match self {
            Boolean => write!(f, "bool"),
            Integer => write!(f, "int"),
            Address => write!(f, "addr"),
            Flags => write!(f, "flags"),
            Size => write!(f, "size"),
            State => write!(f, "state"),
            Interface => write!(f, "interface"),
            Unit => write!(f, "unit"),
        }
    }
}
