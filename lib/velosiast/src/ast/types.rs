// VelosiAst -- a Ast for the Velosiraptor Language
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

//! # VelosiAst -- Type Information
//!
//! This module defines type information nodes of the VelosiAst

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::{VelosiParseTreeType, VelosiParseTreeTypeInfo};

// used crate functionality
use crate::error::VelosiAstIssues;
use crate::{ast_result_return, utils, AstResult, SymbolTable, VelosiTokenStream};

// used definitions of references AST nodes
use crate::ast::VelosiAstIdentifier;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Type Information
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents the type information, either built-in or a type ref to another unit
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum VelosiAstTypeInfo {
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
    /// built in range type
    Range,
    /// type referece to user-define type (unit)
    TypeRef(Rc<String>),
    /// Reference to the state
    State,
    /// Reference to the interface
    Interface,
    /// No type
    Void,
}

impl VelosiAstTypeInfo {
    /// whether or not the type is a built-in type
    pub fn is_builtin(&self) -> bool {
        use VelosiAstTypeInfo::*;
        !matches!(self, TypeRef(_) | State | Interface)
    }

    pub fn is_void(&self) -> bool {
        use VelosiAstTypeInfo::*;
        matches!(self, Void)
    }

    /// whether or not the type is of a numeric kind
    pub fn is_numeric(&self) -> bool {
        use VelosiAstTypeInfo::*;
        matches!(self, Integer | GenAddr | VirtAddr | PhysAddr | Size)
    }

    /// whether or not the type is boolean
    pub fn is_boolean(&self) -> bool {
        matches!(self, VelosiAstTypeInfo::Bool)
    }

    /// whether or not the type is flags
    pub fn is_flags(&self) -> bool {
        matches!(self, VelosiAstTypeInfo::Flags)
    }

    // whether this is an address type
    pub fn is_addr(&self) -> bool {
        use VelosiAstTypeInfo::*;
        matches!(self, GenAddr | VirtAddr | PhysAddr)
    }

    // whether this is a physical address type
    pub fn is_paddr(&self) -> bool {
        matches!(self, Self::PhysAddr)
    }

    // whether this is type refereces of another unit
    pub fn is_typeref(&self) -> bool {
        matches!(self, VelosiAstTypeInfo::TypeRef(_))
    }

    pub fn typeref(&self) -> Option<&Rc<String>> {
        match self {
            VelosiAstTypeInfo::TypeRef(name) => Some(name),
            _ => None,
        }
    }

    /// check whether the type is compatible with the other.
    ///
    /// The two types are compatible if they have the same kind
    /// numeric-numeric, boolean-boolean, flags-flags, or the same
    /// type reference.
    pub fn compatible(&self, other: &Self) -> bool {
        use VelosiAstTypeInfo::*;
        match self {
            Integer => other.is_numeric() || other.is_flags(),
            Bool => other.is_boolean() || other.is_flags(),
            GenAddr => other.is_numeric(),
            VirtAddr => other.is_numeric(),
            PhysAddr => other.is_numeric(),
            Size => other.is_numeric(),
            Flags => other.is_boolean() || other.is_numeric() || other.is_flags(),
            Range => false,
            TypeRef(_) => other.is_numeric(), //self == other,
            State => false,
            Interface => false,
            Void => *other == Void,
        }
    }

    /// obtains the type as a string slices
    pub fn as_str(&self) -> &str {
        use VelosiAstTypeInfo::*;
        match self {
            Integer => "int",
            Bool => "bool",
            GenAddr => "addr",
            VirtAddr => "vaddr",
            PhysAddr => "paddr",
            Size => "size",
            Flags => "flags",
            Range => "range",
            TypeRef(name) => name,
            State => "state",
            Interface => "interface",
            Void => "()",
        }
    }

    /// obtains the type kind
    pub fn as_kind_str(&self) -> &str {
        use VelosiAstTypeInfo::*;

        if self.is_numeric() {
            return "numeric";
        }

        match self {
            Bool => "boolean",
            Flags => "flags",
            Range => "range",
            TypeRef(name) => name,
            State => "state",
            Interface => "interface",
            Void => "void",
            _ => unreachable!(),
        }
    }
}

/// Implementation of [From] for [VelosiAstTypeInfo]
impl From<VelosiParseTreeTypeInfo> for VelosiAstTypeInfo {
    fn from(t: VelosiParseTreeTypeInfo) -> Self {
        use VelosiParseTreeTypeInfo::*;
        match t {
            Integer => VelosiAstTypeInfo::Integer,
            Bool => VelosiAstTypeInfo::Bool,
            GenAddr => VelosiAstTypeInfo::GenAddr,
            VirtAddr => VelosiAstTypeInfo::VirtAddr,
            PhysAddr => VelosiAstTypeInfo::PhysAddr,
            Size => VelosiAstTypeInfo::Size,
            Flags => VelosiAstTypeInfo::Flags,
            TypeRef(s) => VelosiAstTypeInfo::TypeRef(Rc::new(s)),
        }
    }
}

/// Implementation of trait [Display] for [VelosiAstTypeInfo]
impl Display for VelosiAstTypeInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.as_str())
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Type Ast Node
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents the type information
#[derive(Eq, Clone)]
pub struct VelosiAstType {
    /// the type information
    pub typeinfo: VelosiAstTypeInfo,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstType {
    pub fn new(typeinfo: VelosiAstTypeInfo, loc: VelosiTokenStream) -> Self {
        VelosiAstType { typeinfo, loc }
    }

    pub fn new_int() -> Self {
        Self::new(VelosiAstTypeInfo::Integer, VelosiTokenStream::default())
    }

    pub fn new_void() -> Self {
        Self::new(VelosiAstTypeInfo::Void, VelosiTokenStream::default())
    }

    pub fn new_paddr() -> Self {
        Self::new(VelosiAstTypeInfo::PhysAddr, VelosiTokenStream::default())
    }

    pub fn new_bool() -> Self {
        Self::new(VelosiAstTypeInfo::Bool, VelosiTokenStream::default())
    }

    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeType,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // obtain the type information
        let typeinfo = VelosiAstTypeInfo::from(pt.typeinfo);

        let res = VelosiAstType {
            typeinfo,
            loc: pt.loc,
        };

        // check the type reference
        if let VelosiAstTypeInfo::TypeRef(tname) = &res.typeinfo {
            // hacky way for the type check
            let id = VelosiAstIdentifier::new(tname.to_string(), res.loc.clone());
            utils::check_type_exists(&mut issues, st, &id);
            ast_result_return!(res, issues)
        } else {
            // no type reference, built-in types are always ok.
            AstResult::Ok(res)
        }
    }

    /// whether or not the type is a built-in type
    pub fn is_builtin(&self) -> bool {
        self.typeinfo.is_builtin()
    }

    /// whether the type is of a numeric kind
    pub fn is_numeric(&self) -> bool {
        self.typeinfo.is_numeric()
    }

    /// whether or not the type is boolean
    pub fn is_boolean(&self) -> bool {
        self.typeinfo.is_boolean()
    }

    /// whether the type is void
    pub fn is_void(&self) -> bool {
        self.typeinfo.is_void()
    }

    /// whether or not the type is flags
    pub fn is_flags(&self) -> bool {
        self.typeinfo.is_flags()
    }

    // whether this is an address type
    pub fn is_addr(&self) -> bool {
        self.typeinfo.is_addr()
    }

    // whether this is type refereces of another unit
    pub fn is_typeref(&self) -> bool {
        self.typeinfo.is_typeref()
    }

    pub fn typeref(&self) -> Option<&Rc<String>> {
        self.typeinfo.typeref()
    }

    /// check whether the type is compatible with the other.
    ///
    /// The two types are compatible if they have the same kind
    /// numeric-numeric, boolean-boolean, flags-flags, or the same
    /// type reference.
    pub fn compatible(&self, other: &Self) -> bool {
        self.typeinfo.compatible(&other.typeinfo)
    }

    pub fn as_type_kind(&self) -> &str {
        if self.is_numeric() {
            "numeric"
        } else if self.is_boolean() {
            "boolean"
        } else if self.is_flags() {
            "flags"
        } else {
            self.typeinfo.as_str()
        }
    }
}

/// Implementation of [PartialEq] for [VelosiAstType]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstType {
    fn eq(&self, other: &Self) -> bool {
        self.typeinfo == other.typeinfo
    }
}

/// Implementation of [Hash] for [VelosiAstType]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.typeinfo.hash(state);
    }
}

/// Implementation of [From] for [VelosiAstType]
///
/// Conversations from tye type information to the type node with the default tokenstream
impl From<VelosiAstTypeInfo> for VelosiAstType {
    fn from(t: VelosiAstTypeInfo) -> Self {
        VelosiAstType::new(t, VelosiTokenStream::default())
    }
}

/// Implementation of trait [Display] for [VelosiAstType]
impl Display for VelosiAstType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Display::fmt(&self.typeinfo, f)
    }
}

/// Implementation of [Debug] for [VelosiAstType]
impl Debug for VelosiAstType {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
