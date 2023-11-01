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
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::{
    VelosiParseTreeExternType, VelosiParseTreeProperty, VelosiParseTreeType,
    VelosiParseTreeTypeInfo,
};

// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstErrDoubleDef, VelosiAstIssues};
use crate::{
    ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable, VelosiTokenStream,
};

// used definitions of references AST nodes
use crate::ast::{VelosiAstIdentifier, VelosiAstNode};

use super::VelosiAstParam;

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
    /// reference to an external type
    Extern(Rc<String>),
    /// Reference to the state
    State,
    /// Reference to the interface
    Interface,
    /// No type
    Void,
    ///
    SelfType,
}

impl VelosiAstTypeInfo {
    /// whether or not the type is a built-in type
    pub fn is_builtin(&self) -> bool {
        use VelosiAstTypeInfo::*;
        matches!(
            self,
            Integer | Bool | GenAddr | VirtAddr | PhysAddr | Size | Flags | Range | Void
        )
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

    /// whether this is an address type
    pub fn is_addr(&self) -> bool {
        use VelosiAstTypeInfo::*;
        matches!(self, GenAddr | VirtAddr | PhysAddr)
    }

    // whether this is a physical address type
    pub fn is_paddr(&self) -> bool {
        matches!(self, Self::PhysAddr)
    }

    /// whether this is type refereces of another unit
    pub fn is_typeref(&self) -> bool {
        matches!(
            self,
            VelosiAstTypeInfo::TypeRef(_) | VelosiAstTypeInfo::SelfType
        )
    }

    /// wether this type is an externally defined type
    pub fn is_extern(&self) -> bool {
        matches!(self, VelosiAstTypeInfo::Extern(_))
    }

    pub fn typeref(&self) -> Option<&Rc<String>> {
        match self {
            VelosiAstTypeInfo::TypeRef(name) => Some(name),
            VelosiAstTypeInfo::Extern(name) => Some(name),
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
        match (self, other) {
            (Integer, other) => other.is_numeric() || other.is_flags(),
            (Bool, other) => other.is_boolean() || other.is_flags(),
            (GenAddr, other) => other.is_numeric(),
            (VirtAddr, other) => other.is_numeric(),
            (PhysAddr, other) => other.is_numeric(),
            (Size, other) => other.is_numeric(),
            (Flags, other) => other.is_boolean() || other.is_numeric() || other.is_flags(),
            (Range, _other) => false,
            (TypeRef(a), TypeRef(b)) => a == b,
            (TypeRef(_), other) => other.is_numeric(), //self == other,
            (Extern(a), Extern(b)) => a == b,
            (Extern(_), _) => false,
            (State, _) => false,
            (Interface, _) => false,
            (SelfType, SelfType) => true,
            (SelfType, _) => false,
            (Void, other) => *other == Void,
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
            Extern(name) => name,
            State => "state",
            Interface => "interface",
            Void => "()",
            SelfType => "Self",
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
            Extern(name) => name,
            State => "state",
            Interface => "interface",
            Void => "void",
            SelfType => "self",
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

        // check the type reference
        match typeinfo {
            VelosiAstTypeInfo::TypeRef(tname) => {
                // hacky way for the type check, and figure out if it's external
                let id = VelosiAstIdentifier::new(tname.to_string(), pt.loc.clone());
                let typeinfo = if utils::check_type_exists(&mut issues, st, &id) {
                    VelosiAstTypeInfo::Extern(tname)
                } else {
                    VelosiAstTypeInfo::TypeRef(tname)
                };
                ast_result_return!(
                    VelosiAstType {
                        typeinfo,
                        loc: pt.loc,
                    },
                    issues
                )
            }
            VelosiAstTypeInfo::Extern(_) => {
                unreachable!("external types should show up as typerefs")
            }
            typeinfo => {
                // no type reference, built-in types are always ok.
                AstResult::Ok(VelosiAstType {
                    typeinfo,
                    loc: pt.loc,
                })
            }
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

    pub fn is_extern(&self) -> bool {
        self.typeinfo.is_extern()
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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Extern Type NOde
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents the type information
#[derive(Eq, Clone)]
pub struct VelosiAstExternType {
    /// the identifier of the type
    pub ident: VelosiAstIdentifier,
    /// the type information
    pub fields: Vec<Rc<VelosiAstParam>>,
    /// the properties of the type
    pub properties: HashSet<Rc<VelosiAstTypeProperty>>,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstExternType {
    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeExternType,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        let ident = VelosiAstIdentifier::from(pt.ident);
        utils::check_camel_case(&mut issues, &ident);

        let mut fields = Vec::new();
        for field in pt.fields {
            fields.push(Rc::new(ast_result_unwrap!(
                VelosiAstParam::from_parse_tree(field, true, st),
                issues
            )));
        }

        let mut field_map: HashMap<Rc<String>, &VelosiAstParam> = HashMap::new();
        for field in &fields {
            // insert into the symbol table
            if let Some(f) = field_map.get(field.ident()) {
                let err = VelosiAstErrDoubleDef::new(
                    field.path().clone(),
                    field.loc.clone(),
                    f.loc.clone(),
                );
                issues.push(err.into());
            } else {
                field_map.insert(field.ident().clone(), field.as_ref());
            }
        }
        let mut properties = HashSet::new();
        for property in pt.properties {
            properties.insert(Rc::new(ast_result_unwrap!(
                VelosiAstTypeProperty::from_parse_tree(property, st),
                issues
            )));
        }

        ast_result_return!(
            VelosiAstExternType {
                ident,
                fields,
                properties,
                loc: pt.loc
            },
            issues
        )
    }

    pub fn populate_symboltable(&self, varname: &str, st: &mut SymbolTable) {
        for field in &self.fields {
            let name = Rc::new(format!("{}.{}", varname, field.ident()));
            if field.ptype.is_extern() {
                let tname = field
                    .ptype
                    .typeref()
                    .expect("BUG: expected typeref to have a name");
                let ty = match st.lookup(tname) {
                    Some(Symbol {
                        ast_node: VelosiAstNode::ExternType(ty),
                        ..
                    }) => Some(ty.clone()),
                    _ => unreachable!(),
                };
                if let Some(t) = ty {
                    t.populate_symboltable(name.as_str(), st)
                }
            }

            let sym = Symbol::new(
                name,
                field.ptype.clone(),
                VelosiAstNode::Param(field.clone()),
            );
            st.insert(sym)
                .expect("conflict while building the symbol table");
        }
    }
}

impl From<Rc<VelosiAstExternType>> for Symbol {
    fn from(value: Rc<VelosiAstExternType>) -> Self {
        Symbol {
            name: value.ident.ident().clone(),
            typeinfo: VelosiAstType::new(
                VelosiAstTypeInfo::Extern(value.ident.ident().clone()),
                value.loc.clone(),
            ),
            ast_node: VelosiAstNode::ExternType(value),
        }
    }
}

impl From<Rc<VelosiAstExternType>> for VelosiAstTypeInfo {
    fn from(value: Rc<VelosiAstExternType>) -> Self {
        VelosiAstTypeInfo::Extern(value.ident.ident().clone())
    }
}

impl From<&VelosiAstExternType> for VelosiAstTypeInfo {
    fn from(value: &VelosiAstExternType) -> Self {
        VelosiAstTypeInfo::Extern(value.ident.ident().clone())
    }
}

impl From<&str> for VelosiAstExternType {
    fn from(value: &str) -> Self {
        Self {
            ident: value.into(),
            fields: Vec::new(),
            properties: HashSet::new(),
            loc: VelosiTokenStream::default(),
        }
    }
}

/// Implementation of trait [Display] for [VelosiAstExternType]
impl Display for VelosiAstExternType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "extern type {}", self.ident)
    }
}

/// Implementation of [Debug] for [VelosiAstExternType]
impl Debug for VelosiAstExternType {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

/// Implementation of [PartialEq] for [VelosiAstExternType]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstExternType {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident
    }
}

/// Implementation of [Hash] for [VelosiAstExternType]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstExternType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ident.hash(state);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Type Properties
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub enum VelosiAstTypeProperty {
    Frame,
    Descriptor,
    None,
}

impl VelosiAstTypeProperty {
    pub fn from_parse_tree(
        pt: VelosiParseTreeProperty,
        _st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        match pt.ident.name.as_str() {
            "frame" => {
                if !pt.params.is_empty() {
                    let msg = "type property `frame` doesn't support arguments";
                    let hint = "remove these arguments";
                    let err = VelosiAstErrBuilder::err(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(pt.params.first().unwrap().loc.clone())
                        .build();
                    AstResult::Issues(Self::Frame, VelosiAstIssues::from(err))
                } else {
                    AstResult::Ok(Self::Frame)
                }
            }
            "desc" => {
                if !pt.params.is_empty() {
                    let msg = "type property `frame` doesn't support arguments";
                    let hint = "remove these arguments";
                    let err = VelosiAstErrBuilder::err(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(pt.params.first().unwrap().loc.clone())
                        .build();
                    AstResult::Issues(Self::Descriptor, VelosiAstIssues::from(err))
                } else {
                    AstResult::Ok(Self::Descriptor)
                }
            }
            p => {
                let msg = format!("unsupported typeproperty {p}");
                let hint = "supported method properties are `invariant` and `remap`";
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint.to_string())
                    .add_location(pt.loc)
                    .build();
                AstResult::Issues(Self::None, VelosiAstIssues::from(err))
            }
        }
    }
}

impl Display for VelosiAstTypeProperty {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Frame => write!(f, "frame"),
            Self::Descriptor => write!(f, "desc"),
            Self::None => Ok(()),
        }
    }
}

/// Implementation of [Debug] for [VelosiAstTypeProperty]
impl Debug for VelosiAstTypeProperty {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
