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

//! # VelosiAst - Expressions
//!
//! This module contains the definitions of the expression AST nodes.

// modules
mod binop;
mod fncall;
mod ifelse;
mod literals;
mod quantifier;
mod range;
mod slice;
mod unop;

// re-exports
pub use binop::{VelosiAstBinOp, VelosiAstBinOpExpr};
pub use fncall::VelosiAstFnCallExpr;
pub use ifelse::VelosiAstIfElseExpr;
pub use literals::{VelosiAstBoolLiteralExpr, VelosiAstIdentLiteralExpr, VelosiAstNumLiteralExpr};
pub use quantifier::{VelosiAstQuantifier, VelosiAstQuantifierExpr};
pub use range::VelosiAstRangeExpr;
pub use slice::VelosiAstSliceExpr;
pub use unop::{VelosiAstUnOp, VelosiAstUnOpExpr};

// used standard library functionality
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::Hash;
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeExpr;
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::VelosiAstIssues;
use crate::{AstResult, SymbolTable};

// used definitions of references AST nodes
use crate::ast::{VelosiAstParam, VelosiAstTypeInfo};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Expressions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents an expression in the parse tree
#[derive(PartialEq, Eq, Hash, Clone)]
pub enum VelosiAstExpr {
    IdentLiteral(VelosiAstIdentLiteralExpr),
    NumLiteral(VelosiAstNumLiteralExpr),
    BoolLiteral(VelosiAstBoolLiteralExpr),
    BinOp(VelosiAstBinOpExpr),
    UnOp(VelosiAstUnOpExpr),
    Quantifier(VelosiAstQuantifierExpr),
    FnCall(VelosiAstFnCallExpr),
    IfElse(VelosiAstIfElseExpr),
    Slice(VelosiAstSliceExpr),
    Range(VelosiAstRangeExpr),
}

impl VelosiAstExpr {
    pub fn from_parse_tree(
        p: VelosiParseTreeExpr,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstExpr, VelosiAstIssues> {
        use VelosiParseTreeExpr::*;
        match p {
            Identifier(e) => VelosiAstIdentLiteralExpr::from_parse_tree(e, st),
            NumLiteral(e) => VelosiAstNumLiteralExpr::from_parse_tree(e, st),
            BoolLiteral(e) => VelosiAstBoolLiteralExpr::from_parse_tree(e, st),
            BinOp(e) => VelosiAstBinOpExpr::from_parse_tree(e, st),
            UnOp(e) => VelosiAstUnOpExpr::from_parse_tree(e, st),
            Quantifier(e) => VelosiAstQuantifierExpr::from_parse_tree(e, st),
            FnCall(e) => VelosiAstFnCallExpr::from_parse_tree(e, st),
            IfElse(e) => VelosiAstIfElseExpr::from_parse_tree(e, st),
            Slice(e) => VelosiAstSliceExpr::from_parse_tree(e, st),
            Range(e) => VelosiAstRangeExpr::from_parse_tree(e, st),
            Element(_e) => panic!("handle me!"),
        }
    }

    fn needs_paren(&self) -> bool {
        matches!(self, VelosiAstExpr::BinOp(_) | VelosiAstExpr::Quantifier(_))
    }

    pub fn loc(&self) -> &VelosiTokenStream {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(e) => &e.loc,
            NumLiteral(e) => &e.loc,
            BoolLiteral(e) => &e.loc,
            BinOp(e) => &e.loc,
            UnOp(e) => &e.loc,
            Quantifier(e) => &e.loc,
            FnCall(e) => &e.loc,
            IfElse(e) => &e.loc,
            Slice(e) => &e.loc,
            Range(e) => &e.loc,
        }
    }

    pub fn is_const_expr(&self) -> bool {
        use VelosiAstExpr::*;
        // when forming the expressions we do constant folding, so the
        // result should only be constant if its a literal
        matches!(self, NumLiteral(_) | BoolLiteral(_))
    }

    // obtains the result of a const expression returning an numeric value
    pub fn const_expr_result_num(&self) -> Option<u64> {
        use VelosiAstExpr::*;
        match self {
            NumLiteral(e) => Some(e.val),
            _ => None,
        }
    }

    // obtains the result type of the epxression
    pub fn result_type(&self) -> &VelosiAstTypeInfo {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(e) => e.result_type(),
            NumLiteral(_) => &VelosiAstTypeInfo::Integer,
            BoolLiteral(_) => &VelosiAstTypeInfo::Bool,
            BinOp(e) => e.result_type(),
            UnOp(e) => e.result_type(),
            Quantifier(_) => &VelosiAstTypeInfo::Bool,
            FnCall(e) => e.result_type(),
            IfElse(e) => e.result_type(),
            Slice(e) => e.result_type(),
            Range(_) => &VelosiAstTypeInfo::Range,
        }
    }

    pub fn flatten(
        self,
        st: &mut SymbolTable,
        mapping: &HashMap<Rc<String>, &VelosiAstExpr>,
    ) -> Self {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(e) => e.flatten(st, mapping),
            BinOp(e) => e.flatten(st, mapping),
            UnOp(e) => e.flatten(st, mapping),
            Quantifier(e) => e.flatten(st, mapping),
            FnCall(e) => e.flatten(st, mapping),
            IfElse(e) => e.flatten(st, mapping),
            Slice(e) => e.flatten(st, mapping),
            Range(e) => e.flatten(st, mapping),
            _ => self,
        }
    }

    pub fn has_interface_references(&self) -> bool {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(i) => i.has_interface_references(),
            NumLiteral(i) => i.has_interface_references(),
            BoolLiteral(i) => i.has_interface_references(),
            BinOp(i) => i.has_interface_references(),
            UnOp(i) => i.has_interface_references(),
            Quantifier(i) => i.has_interface_references(),
            FnCall(i) => i.has_interface_references(),
            IfElse(i) => i.has_interface_references(),
            Slice(i) => i.has_interface_references(),
            Range(i) => i.has_interface_references(),
        }
    }

    pub fn has_state_references(&self) -> bool {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(i) => i.has_state_references(),
            NumLiteral(i) => i.has_state_references(),
            BoolLiteral(i) => i.has_state_references(),
            BinOp(i) => i.has_state_references(),
            UnOp(i) => i.has_state_references(),
            Quantifier(i) => i.has_state_references(),
            FnCall(i) => i.has_state_references(),
            IfElse(i) => i.has_state_references(),
            Slice(i) => i.has_state_references(),
            Range(i) => i.has_state_references(),
        }
    }

    pub fn has_var_references(&self, vars: &HashSet<&str>) -> bool {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(i) => i.has_var_references(vars),
            NumLiteral(i) => i.has_var_references(vars),
            BoolLiteral(i) => i.has_var_references(vars),
            BinOp(i) => i.has_var_references(vars),
            UnOp(i) => i.has_var_references(vars),
            Quantifier(i) => i.has_var_references(vars),
            FnCall(i) => i.has_var_references(vars),
            IfElse(i) => i.has_var_references(vars),
            Slice(i) => i.has_var_references(vars),
            Range(i) => i.has_var_references(vars),
        }
    }

    pub fn get_var_references(&self) -> HashSet<&VelosiAstIdentLiteralExpr> {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(i) => i.get_var_references(),
            NumLiteral(i) => i.get_var_references(),
            BoolLiteral(i) => i.get_var_references(),
            BinOp(i) => i.get_var_references(),
            UnOp(i) => i.get_var_references(),
            Quantifier(i) => i.get_var_references(),
            FnCall(i) => i.get_var_references(),
            IfElse(i) => i.get_var_references(),
            Slice(i) => i.get_var_references(),
            Range(i) => i.get_var_references(),
        }
    }

    pub fn get_state_references(&self, srefs: &mut HashSet<Rc<String>>) {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(i) => i.get_state_references(srefs),
            NumLiteral(i) => i.get_state_references(srefs),
            BoolLiteral(i) => i.get_state_references(srefs),
            BinOp(i) => i.get_state_references(srefs),
            UnOp(i) => i.get_state_references(srefs),
            Quantifier(i) => i.get_state_references(srefs),
            FnCall(i) => i.get_state_references(srefs),
            IfElse(i) => i.get_state_references(srefs),
            Slice(i) => i.get_state_references(srefs),
            Range(i) => i.get_state_references(srefs),
        };
    }

    pub fn get_interface_references(&self, irefs: &mut HashSet<Rc<String>>) {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(i) => i.get_interface_references(irefs),
            NumLiteral(i) => i.get_interface_references(irefs),
            BoolLiteral(i) => i.get_interface_references(irefs),
            BinOp(i) => i.get_interface_references(irefs),
            UnOp(i) => i.get_interface_references(irefs),
            Quantifier(i) => i.get_interface_references(irefs),
            FnCall(i) => i.get_interface_references(irefs),
            IfElse(i) => i.get_interface_references(irefs),
            Slice(i) => i.get_interface_references(irefs),
            Range(i) => i.get_interface_references(irefs),
        };
    }

    // converts a boolean expression into the conjunctive normal form
    pub fn into_cnf(self, st: &mut SymbolTable) -> Self {
        use VelosiAstBinOp::*;
        use VelosiAstExpr::*;
        use VelosiAstUnOp::*;

        let mapping = HashMap::new();

        if let BinOp(outer) = &self {
            // distributive law

            // (p or (q and r)) == (p or q) and (p or r)
            if let BinOp(inner) = outer.rhs.as_ref() {
                if outer.op == Lor && inner.op == Land {
                    let lhs = VelosiAstBinOpExpr::new(
                        outer.lhs.clone(),
                        Lor,
                        inner.lhs.clone(),
                        outer.loc.clone(),
                    )
                    .flatten(st, &mapping);
                    let rhs = VelosiAstBinOpExpr::new(
                        outer.lhs.clone(),
                        Lor,
                        inner.rhs.clone(),
                        outer.loc.clone(),
                    )
                    .flatten(st, &mapping);
                    let res = VelosiAstBinOpExpr::new(
                        Rc::new(lhs),
                        Land,
                        Rc::new(rhs),
                        outer.loc.clone(),
                    )
                    .flatten(st, &mapping);
                    // println!("into_cnf | rewrite: applying distributive law");
                    // println!("  {} -> {}", self, res);
                    return res;
                }
            }

            // ((q and r) or p) == (p or q) and (p or r)
            if let BinOp(inner) = outer.lhs.as_ref() {
                if outer.op == Lor && inner.op == Land {
                    // println!("into_cnf | rewrite: applying distributive law");
                    let lhs = VelosiAstBinOpExpr::new(
                        outer.rhs.clone(),
                        Lor,
                        inner.lhs.clone(),
                        outer.loc.clone(),
                    )
                    .flatten(st, &mapping);
                    let rhs = VelosiAstBinOpExpr::new(
                        outer.rhs.clone(),
                        Lor,
                        inner.rhs.clone(),
                        outer.loc.clone(),
                    )
                    .flatten(st, &mapping);
                    let res = VelosiAstBinOpExpr::new(
                        Rc::new(lhs),
                        Land,
                        Rc::new(rhs),
                        outer.loc.clone(),
                    )
                    .flatten(st, &mapping);
                    // println!("into_cnf | rewrite: applying distributive law");
                    // println!("  {} -> {}", self, res);
                    return res;
                }
            }
        } else if let UnOp(ue) = &self {
            if let BinOp(be) = ue.expr.as_ref() {
                // demorgan's law
                // !(p or q) == !p and !q
                if ue.op == LNot && be.op == Lor {
                    let lhs = VelosiAstUnOpExpr::new(LNot, be.lhs.clone(), be.loc.clone())
                        .flatten(st, &mapping);
                    let rhs = VelosiAstUnOpExpr::new(LNot, be.rhs.clone(), be.loc.clone())
                        .flatten(st, &mapping);
                    let res =
                        VelosiAstBinOpExpr::new(Rc::new(lhs), Land, Rc::new(rhs), ue.loc.clone())
                            .flatten(st, &mapping);
                    // println!("into_cnf | rewrite: applying demorgan's law");
                    // println!("  {} -> {}", self, res);
                    return res;
                }
            }
        }
        self
    }

    /// splits a boolean expression into is conjuncts
    pub fn split_cnf(&self) -> Vec<Rc<Self>> {
        use VelosiAstExpr::*;
        match self {
            BinOp(e) => {
                if e.op == VelosiAstBinOp::Land {
                    let mut v = e.lhs.split_cnf();
                    v.extend(e.rhs.split_cnf());
                    v
                } else {
                    vec![BinOp(e.clone()).into()]
                }
            }
            e => vec![e.clone().into()],
        }
    }

    /// returns true if the expression is an lvalue
    pub fn is_lvalue(&self) -> bool {
        use VelosiAstExpr::*;
        matches!(self, IdentLiteral(_) | Slice(_))
    }
}

impl Ord for VelosiAstExpr {
    fn cmp(&self, other: &Self) -> Ordering {
        use VelosiAstExpr::*;

        // Range == Slice == Quantifier == FnCall == IfElse < BinOp < UnOp < IdentLit < NumLit == BoolLit

        match (self, other) {
            (NumLiteral(_), NumLiteral(_)) => Ordering::Equal,
            (NumLiteral(_), BoolLiteral(_)) => Ordering::Equal,
            (BoolLiteral(_), BoolLiteral(_)) => Ordering::Equal,
            (BoolLiteral(_), NumLiteral(_)) => Ordering::Equal,

            (NumLiteral(_), _) => Ordering::Greater,
            (BoolLiteral(_), _) => Ordering::Greater,
            (_, NumLiteral(_)) => Ordering::Less,
            (_, BoolLiteral(_)) => Ordering::Less,

            (IdentLiteral(_), IdentLiteral(_)) => Ordering::Equal,
            (IdentLiteral(_), _) => Ordering::Greater,
            (_, IdentLiteral(_)) => Ordering::Less,

            (UnOp(_), UnOp(_)) => Ordering::Equal,
            (UnOp(_), _) => Ordering::Greater,
            (_, UnOp(_)) => Ordering::Less,

            (BinOp(_), _) => Ordering::Greater,
            (_, BinOp(_)) => Ordering::Less,

            _ => Ordering::Equal, // (Quantifier(_), Quantifier(_)) => {Ordering::Equal}
                                  // (FnCall(_), FnCall(_)) => {Ordering::Equal}
                                  // (IfElse(_), IfElse(_)) => {Ordering::Equal}
                                  // (Slice(_), Slice(_)) => {Ordering::Equal}
                                  // (Range(_), Range(_)) => {Ordering::Equal}
        }
    }
}

impl PartialOrd for VelosiAstExpr {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Implementation of [Display] for [VelosiAstExpr]
impl Display for VelosiAstExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        use VelosiAstExpr::*;
        match self {
            IdentLiteral(i) => Display::fmt(&i, format),
            NumLiteral(i) => Display::fmt(&i, format),
            BoolLiteral(i) => Display::fmt(&i, format),
            BinOp(i) => Display::fmt(&i, format),
            UnOp(i) => Display::fmt(&i, format),
            Quantifier(i) => Display::fmt(&i, format),
            FnCall(i) => Display::fmt(&i, format),
            IfElse(i) => Display::fmt(&i, format),
            Slice(i) => Display::fmt(&i, format),
            Range(i) => Display::fmt(&i, format),
        }
    }
}

/// Implementation of [Debug] for [VelosiAstExpr]
impl Debug for VelosiAstExpr {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}

impl From<&VelosiAstParam> for VelosiAstExpr {
    fn from(p: &VelosiAstParam) -> Self {
        VelosiAstExpr::IdentLiteral(VelosiAstIdentLiteralExpr::new(
            vec![p.ident.clone()],
            p.ptype.typeinfo.clone(),
            p.loc.clone(),
        ))
    }
}
