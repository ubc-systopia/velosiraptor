// VelosiParser -- a parser for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2021, 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiParser -- Parse Tree Type Node
//!
//! Parse tree nodes for type information

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

// use crate functionality
use crate::parsetree::VelosiParseTreeIdentifier;
use crate::VelosiTokenStream;

use super::VelosiParseTreeParam;

/// Represents the type information, either built in or a type ref
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum VelosiParseTreeTypeInfo {
    /// built-in integer type
    Integer,
    /// built-in boolean type
    Bool,
    /// built-in generic address type
    GenAddr,
    /// built-in virtual address type
    VirtAddr,
    /// built-in physical address type
    PhysAddr,
    /// built-in size type
    Size,
    /// built-in flags type
    Flags,
    /// type referece to user-define type
    TypeRef(String),
}

impl VelosiParseTreeTypeInfo {
    /// whether or not the type is a built-in type
    pub fn is_builtin(&self) -> bool {
        matches!(self, VelosiParseTreeTypeInfo::TypeRef(_))
    }
}

impl From<VelosiParseTreeIdentifier> for VelosiParseTreeTypeInfo {
    fn from(id: VelosiParseTreeIdentifier) -> Self {
        VelosiParseTreeTypeInfo::TypeRef(id.name)
    }
}

/// Implementation of trait [Display] for [VelosiParseTreeTypeInfo]
impl Display for VelosiParseTreeTypeInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use VelosiParseTreeTypeInfo::*;
        match self {
            Integer => write!(f, "int"),
            Bool => write!(f, "bool"),
            GenAddr => write!(f, "addr"),
            VirtAddr => write!(f, "vaddr"),
            PhysAddr => write!(f, "paddr"),
            Size => write!(f, "size"),
            Flags => write!(f, "flags"),
            TypeRef(name) => write!(f, "{name}"),
        }
    }
}

/// Represents the type information
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeType {
    /// the type information
    pub typeinfo: VelosiParseTreeTypeInfo,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeType {
    /// Creates a new type tree node with the given type
    pub fn new(typeinfo: VelosiParseTreeTypeInfo, loc: VelosiTokenStream) -> Self {
        VelosiParseTreeType { typeinfo, loc }
    }
}

/// Implementation of trait [Display] for [VelosiParseTreeType]
impl Display for VelosiParseTreeType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Display::fmt(&self.typeinfo, f)
    }
}

/// Implementation of [Debug] for [VelosiParseTreeType]
impl Debug for VelosiParseTreeType {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Extern Types
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents the type information
#[derive(PartialEq, Eq, Clone)]
pub struct VelosiParseTreeExternType {
    /// the identifier of the type
    pub ident: VelosiParseTreeIdentifier,
    /// the type information
    pub fields: Vec<VelosiParseTreeParam>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiParseTreeExternType {
    pub fn loc(&self) -> &VelosiTokenStream {
        &self.loc
    }
}

/// Implementation of trait [Display] for [VelosiParseTreeExternType]
impl Display for VelosiParseTreeExternType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "extern type {} {{", self.ident)?;
        for field in &self.fields {
            writeln!(f, "  {field}")?;
        }
        writeln!(f, "}}")
    }
}

/// Implementation of [Debug] for [VelosiParseTreeExternType]
impl Debug for VelosiParseTreeExternType {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
