// Velosiraptor AST
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

//! # VelosiAst - Literal Expressions
//!
//! This module contains the definitions of the binary, numeric and identifier literal expressions
//! AST nodes.

// used standard library functionality
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::{
    VelosiParseTreeBoolLiteral, VelosiParseTreeIdentifierLiteral, VelosiParseTreeNumLiteral,
    VelosiTokenStream,
};

// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstErrUndef, VelosiAstIssues};
use crate::{AstResult, SymbolTable, VelosiAstFieldSlice};

// used definitions of references AST nodes
use crate::ast::{VelosiAstExpr, VelosiAstIdentifier, VelosiAstNode, VelosiAstTypeInfo};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Identifier Literal Expressions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an identifier literal expression
#[derive(Eq, Clone)]
pub struct VelosiAstIdentLiteralExpr {
    pub ident: VelosiAstIdentifier,
    pub etype: VelosiAstTypeInfo,
    pub loc: VelosiTokenStream,
}

use core::str::Split;

impl VelosiAstIdentLiteralExpr {
    pub fn new(
        path: Vec<VelosiAstIdentifier>,
        etype: VelosiAstTypeInfo,
        loc: VelosiTokenStream,
    ) -> Self {
        let mut ident = path.first().unwrap().clone();
        for p in path.into_iter().skip(1) {
            ident.extend(p);
        }

        VelosiAstIdentLiteralExpr { ident, etype, loc }
    }

    pub fn with_name(name: String, ptype: VelosiAstTypeInfo) -> Self {
        VelosiAstIdentLiteralExpr::new(
            vec![VelosiAstIdentifier::with_name(name)],
            ptype,
            VelosiTokenStream::empty(),
        )
    }

    pub fn from_parse_tree(
        p: VelosiParseTreeIdentifierLiteral,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        // lookup the symbol in the symbol table

        let path = p
            .path
            .into_iter()
            .map(VelosiAstIdentifier::from)
            .collect::<Vec<VelosiAstIdentifier>>();

        let mut litexpr = VelosiAstIdentLiteralExpr::new(path, VelosiAstTypeInfo::Integer, p.loc);

        let tname = litexpr.path();
        let sym = st.lookup(tname);
        if sym.is_none() {
            let err = VelosiAstErrUndef::new(litexpr.ident().clone(), litexpr.loc.clone());
            return AstResult::Issues(VelosiAstExpr::IdentLiteral(litexpr), err.into());
        }

        let sym = sym.unwrap();

        match &sym.ast_node {
            VelosiAstNode::Const(c) => {
                debug_assert!(c.value.is_const_expr());
                // replace the identifier with the constant value
                AstResult::Ok(c.value.clone())
            }
            VelosiAstNode::Param(p) => {
                litexpr.etype = p.ptype.typeinfo.clone();
                AstResult::Ok(VelosiAstExpr::IdentLiteral(litexpr))
            }
            VelosiAstNode::StateField(f) => {
                Self::handle_field_reference(f.layout_as_slice(), litexpr, st)
            }
            VelosiAstNode::StateFieldSlice(_) => {
                AstResult::Ok(VelosiAstExpr::IdentLiteral(litexpr))
            }
            VelosiAstNode::InterfaceField(f) => {
                Self::handle_field_reference(f.layout_as_slice(), litexpr, st)
            }
            VelosiAstNode::InterfaceFieldSlice(_) => {
                AstResult::Ok(VelosiAstExpr::IdentLiteral(litexpr))
            }
            VelosiAstNode::Flag(_) => {
                litexpr.etype = VelosiAstTypeInfo::Flags;
                AstResult::Ok(VelosiAstExpr::IdentLiteral(litexpr))
            }
            _ => {
                // we have the wrong kind of symbol
                let err = VelosiAstErrUndef::with_other(
                    litexpr.path().clone(),
                    litexpr.loc.clone(),
                    sym.loc().clone(),
                );
                AstResult::Issues(VelosiAstExpr::IdentLiteral(litexpr), err.into())
            }
        }
    }

    pub fn flatten(
        self,
        st: &mut SymbolTable,
        mapping: &HashMap<Rc<String>, &VelosiAstExpr>,
    ) -> VelosiAstExpr {
        let sym = st.lookup(self.path());
        if let Some(sym) = sym {
            match &sym.ast_node {
                VelosiAstNode::Const(c) => c.value.clone(),
                _ => VelosiAstExpr::IdentLiteral(self),
            }
        } else if let Some(expr) = mapping.get(self.path()) {
            (*expr).clone()
        } else {
            VelosiAstExpr::IdentLiteral(self)
        }
    }

    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        &self.etype
    }

    /// obtains a reference to the identifier
    pub fn ident(&self) -> &Rc<String> {
        self.ident.ident()
    }

    /// obtains a copy of the identifer
    pub fn ident_to_string(&self) -> String {
        self.ident.as_str().to_string()
    }

    /// obtains a reference to the fully qualified path
    pub fn path(&self) -> &Rc<String> {
        &self.ident.path
    }

    pub fn path_split(&'_ self) -> Split<&'_ str> {
        self.ident.path_split()
    }

    /// obtains a copy of the fully qualified path
    pub fn path_to_string(&self) -> String {
        self.ident.path.as_str().to_string()
    }

    pub fn get_interface_references(&self, irefs: &mut HashSet<Rc<String>>) {
        if self.has_interface_references() {
            irefs.insert(self.path().clone());
        }
    }

    pub fn get_state_references(&self, srefs: &mut HashSet<Rc<String>>) {
        if self.has_state_references() {
            srefs.insert(self.path().clone());
        }
    }

    pub fn has_state_references(&self) -> bool {
        self.path().starts_with("state")
    }

    pub fn has_var_references(&self, vars: &HashSet<&str>) -> bool {
        vars.contains(self.path().as_str())
        // sort of a hack to support flgs.foo
        || (vars.contains("flgs") && self.path().starts_with("flgs"))
    }

    pub fn has_interface_references(&self) -> bool {
        self.path().starts_with("interface")
    }

    fn handle_field_reference(
        layout: &[Rc<VelosiAstFieldSlice>],
        mut litexpr: VelosiAstIdentLiteralExpr,
        st: &SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        match layout {
            [field_slice] => {
                litexpr.ident.extend_with_str(&field_slice.ident.ident);
                AstResult::Ok(VelosiAstExpr::IdentLiteral(litexpr))
            }
            _ => {
                let msg = "taking the whole field with more than one slice is not supported";
                let hint = "specify a slice of this field";
                let related = "or remove slices from the field definition";
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(litexpr.loc.clone())
                    .add_related_location(
                        related.to_string(),
                        st.lookup(&litexpr.ident_to_string()).unwrap().loc().clone(),
                    )
                    .build();
                AstResult::Issues(VelosiAstExpr::IdentLiteral(litexpr), err.into())
            }
        }
    }

    pub fn get_var_references(&self) -> HashSet<&VelosiAstIdentLiteralExpr> {
        let mut vars = HashSet::new();
        if !(self.has_state_references() || self.has_interface_references()) {
            vars.insert(self);
        }
        vars
    }
}

/// Implementation of [PartialEq] for [VelosiAstIdentLiteralExpr]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstIdentLiteralExpr {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident && self.etype == other.etype
    }
}

/// Implementation of [Hash] for [VelosiAstIdentLiteralExpr]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstIdentLiteralExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ident.hash(state);
        self.etype.hash(state);
    }
}

/// Implementation of [Display] for [VelosiAstIdentLiteralExpr]
impl Display for VelosiAstIdentLiteralExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}", self.path())
    }
}

/// Implementation of [Debug] for [VelosiAstIdentLiteralExpr]
impl Debug for VelosiAstIdentLiteralExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Numeric Literal Expressions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an numeric literal expression
#[derive(Eq, Clone)]
pub struct VelosiAstNumLiteralExpr {
    pub val: u64,
    pub loc: VelosiTokenStream,
}

impl VelosiAstNumLiteralExpr {
    pub fn new(val: u64, loc: VelosiTokenStream) -> Self {
        VelosiAstNumLiteralExpr { val, loc }
    }

    pub fn from_parse_tree(
        p: VelosiParseTreeNumLiteral,
        _st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        // we can just convert the literal, as all values should be fine
        let e = VelosiAstNumLiteralExpr::new(p.value, p.loc);
        AstResult::Ok(VelosiAstExpr::NumLiteral(e))
    }

    pub fn get_interface_references(&self, _irefs: &mut HashSet<Rc<String>>) {
        /* no-op */
    }

    pub fn get_state_references(&self, _srefs: &mut HashSet<Rc<String>>) {
        /* no-op */
    }

    pub fn has_state_references(&self) -> bool {
        false
    }

    pub fn has_interface_references(&self) -> bool {
        false
    }

    pub fn has_var_references(&self, _vars: &HashSet<&str>) -> bool {
        false
    }

    pub fn get_var_references(&self) -> HashSet<&VelosiAstIdentLiteralExpr> {
        HashSet::new()
    }
}

/// Implementation of [PartialEq] for [VelosiAstNumLiteralExpr]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstNumLiteralExpr {
    fn eq(&self, other: &Self) -> bool {
        self.val == other.val
    }
}

/// Implementation of [Hash] for [VelosiAstNumLiteralExpr]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstNumLiteralExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.val.hash(state);
    }
}

/// Implementation of [Display] for [VelosiAstNumLiteralExpr]
impl Display for VelosiAstNumLiteralExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "0x{:x}", self.val)
    }
}

impl From<u64> for VelosiAstNumLiteralExpr {
    fn from(val: u64) -> Self {
        Self::new(val, VelosiTokenStream::default())
    }
}

/// Implementation of [Debug] for [VelosiAstNumLiteralExpr]
impl Debug for VelosiAstNumLiteralExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Boolean Literal Expressions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an boolean literal expression
#[derive(Eq, Clone)]
pub struct VelosiAstBoolLiteralExpr {
    pub val: bool,
    pub loc: VelosiTokenStream,
}

impl VelosiAstBoolLiteralExpr {
    pub fn btrue() -> Self {
        Self::new(true, VelosiTokenStream::default())
    }

    pub fn bfalse() -> Self {
        Self::new(false, VelosiTokenStream::default())
    }

    pub fn new(val: bool, loc: VelosiTokenStream) -> Self {
        VelosiAstBoolLiteralExpr { val, loc }
    }

    pub fn from_parse_tree(
        p: VelosiParseTreeBoolLiteral,
        _st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        // we can just convert the literal, as all values should be fine
        let e = VelosiAstBoolLiteralExpr::new(p.value, p.loc);
        AstResult::Ok(VelosiAstExpr::BoolLiteral(e))
    }

    pub fn get_interface_references(&self, _irefs: &mut HashSet<Rc<String>>) {
        /* no-op */
    }

    pub fn get_state_references(&self, _srefs: &mut HashSet<Rc<String>>) {
        /* no op */
    }

    pub fn has_state_references(&self) -> bool {
        false
    }

    pub fn has_interface_references(&self) -> bool {
        false
    }

    pub fn has_var_references(&self, _vars: &HashSet<&str>) -> bool {
        false
    }

    pub fn get_var_references(&self) -> HashSet<&VelosiAstIdentLiteralExpr> {
        HashSet::new()
    }
}

/// Implementation of [PartialEq] for [VelosiAstBoolLiteralExpr]
///
/// We implement our own variant of partial equality as we do not want to consider the
/// location of the expression when comparing two expressions.
impl PartialEq for VelosiAstBoolLiteralExpr {
    fn eq(&self, other: &Self) -> bool {
        self.val == other.val
    }
}

/// Implementation of [Hash] for [VelosiAstBoolLiteralExpr]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions.
impl Hash for VelosiAstBoolLiteralExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.val.hash(state);
    }
}

impl From<bool> for VelosiAstBoolLiteralExpr {
    fn from(val: bool) -> Self {
        Self::new(val, VelosiTokenStream::default())
    }
}

/// Implementation of [Display] for [VelosiAstBoolLiteralExpr]
impl Display for VelosiAstBoolLiteralExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        write!(format, "{}", self.val)
    }
}

/// Implementation of [Debug] for [VelosiAstBoolLiteralExpr]
impl Debug for VelosiAstBoolLiteralExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
