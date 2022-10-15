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

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// parser types
use velosiparser::{VelosiParseTreeType, VelosiParseTreeTypeInfo};

// use crate functionality
use crate::VelosiTokenStream;

use crate::ast::VelosiAstNode;
use crate::error::{VelosiAstErr, VelosiAstErrUndef};
use crate::{AstResult, SymbolTable};

/// Represents the type information, either built in or a type ref
#[derive(PartialEq, Eq, Clone, Debug)]
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
    /// type referece to user-define type
    TypeRef(Rc<String>),
}

impl VelosiAstTypeInfo {
    /// whether or not the type is a built-in type
    pub fn is_builtin(&self) -> bool {
        matches!(self, VelosiAstTypeInfo::TypeRef(_))
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
        use VelosiAstTypeInfo::*;
        match self {
            Integer => write!(f, "int"),
            Bool => write!(f, "bool"),
            GenAddr => write!(f, "addr"),
            VirtAddr => write!(f, "vaddr"),
            PhysAddr => write!(f, "paddr"),
            Size => write!(f, "size"),
            Flags => write!(f, "flags"),
            TypeRef(name) => write!(f, "{}", name),
        }
    }
}

/// Represents the type information
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstType {
    /// the type information
    pub typeinfo: VelosiAstTypeInfo,
    /// the location of the type clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstType {
    pub fn from_parse_tree(
        pt: VelosiParseTreeType,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstErr> {
        let typeinfo = VelosiAstTypeInfo::from(pt.typeinfo);

        let res = VelosiAstType {
            typeinfo,
            loc: pt.loc,
        };

        if let VelosiAstTypeInfo::TypeRef(tname) = &res.typeinfo {
            if let Some(s) = st.lookup(tname.as_str()) {
                match s.ast_node {
                    VelosiAstNode::Unit(_) => {
                        // there is a symbol with that type
                        AstResult::Ok(res)
                    }
                    _ => {
                        // report that there was a mismatching type
                        let err = VelosiAstErrUndef::with_other(
                            tname.clone(),
                            res.loc.clone(),
                            s.loc().clone(),
                        );
                        AstResult::Issues(res, err.into())
                    }
                }
            } else {
                // there is no such type, still create the node and report the issue
                let err = VelosiAstErrUndef::new(tname.clone(), res.loc.clone());
                AstResult::Issues(res, err.into())
            }
        } else {
            AstResult::Ok(res)
        }
    }
}

/// Implementation of trait [Display] for [VelosiAstType]
impl Display for VelosiAstType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Display::fmt(&self.typeinfo, f)
    }
}
