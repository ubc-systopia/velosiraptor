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

use std::collections::HashSet;
///! Statement module
// std lib imports
use std::fmt;

// library internal imports
use crate::ast::{AstNode, AstNodeGeneric, Expr, Issues, Symbol, SymbolKind, SymbolTable, Type};
use crate::error::VrsError;
use crate::token::TokenStream;

/// Represents a statement
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Stmt {
    /// represents a block of statements
    Block { pos: TokenStream, stmts: Vec<Stmt> },
    /// the assign statements gives a name to a value
    Let {
        pos: TokenStream,
        typeinfo: Type,
        lhs: String,
        rhs: Expr,
    },
    /// the conditional with
    IfElse {
        pos: TokenStream,
        cond: Expr,
        then: Box<Stmt>,
        other: Box<Option<Stmt>>,
    },
    /// return statement
    Return { pos: TokenStream, expr: Expr },
    /// assert statement
    Assert { pos: TokenStream, expr: Expr },
}

/// implementation of [Stmt]
impl Stmt {
    pub fn check_return_types(&self, ty: Type, st: &SymbolTable) -> Issues {
        use Stmt::*;
        match self {
            Block { stmts, pos } => {
                let mut issues = Issues::ok();
                let mut had_return = false;
                for s in stmts {
                    // recurse into the statement
                    issues = issues + s.check_return_types(ty, st);
                    if had_return {
                        // we've already seen a return statement, so this is now dead code.
                        let msg = String::from("statement after return statement");
                        let hint = String::from("remove dead code here");
                        VrsError::new_warn(s.loc(), msg, Some(hint)).print();

                        issues.inc_warn(1);
                    } else if let Return { .. } = s {
                        // if it was a return statement, then mark it
                        had_return = true;
                    }
                    // otherwise there is no return statement, and we haven't seen one yet
                }
                if !had_return {
                    // we haven't seen any return statement in this branch, this is a bug.
                    // note: this is currently only true because of the restrictive way branches
                    //       are handled and may be revisited in the future
                    let msg = String::from("no return statement in statement block");
                    let hint = String::from("add a return statement here");
                    let loc = match stmts.last() {
                        Some(x) => x.loc(),
                        None => pos,
                    };
                    VrsError::new_err(loc, msg, Some(hint)).print();
                    issues.inc_err(1);
                }
                issues
            }
            IfElse { then, other, .. } => {
                let issues = then.check_return_types(ty, st);
                match other.as_ref() {
                    None => issues,
                    Some(b) => issues + b.check_return_types(ty, st),
                }
            }
            // let is a no-po
            Let { .. } => Issues::ok(),
            // assert is a no-op
            Assert { .. } => Issues::ok(),
            // return
            Return { expr, .. } => {
                // check the return type
                expr.match_type(ty, st)
            }
        }
    }

    /// returns a list of state references made by this statemet
    pub fn get_state_references(&self) -> HashSet<String> {
        use Stmt::*;
        match self {
            Block { stmts, .. } => stmts
                .iter()
                .flat_map(|s| s.get_state_references())
                .collect(),
            Let { rhs, .. } => rhs.get_state_references(),
            IfElse { then, other, .. } => {
                let mut v = then.get_state_references();
                if let Some(b) = other.as_ref() {
                    v.extend(b.get_state_references());
                }
                v
            }
            Return { expr, .. } => expr.get_state_references(),
            Assert { expr, .. } => expr.get_state_references(),
        }
    }
}

/// implementation of [fmt::Display] for [Stmt]
impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Stmt::*;
        match self {
            Block { stmts, .. } => {
                writeln!(f, "{{")?;
                for s in stmts {
                    writeln!(f, "{}", s)?;
                }
                writeln!(f, "}}")
            }
            Return { expr, .. } => {
                writeln!(f, "return {};", expr)
            }
            Let {
                typeinfo,
                lhs,
                rhs,
                pos: _,
            } => writeln!(f, "let {} : {} = {};", typeinfo, lhs, rhs),
            Assert { expr, pos: _ } => writeln!(f, "assert {};", expr),
            IfElse {
                cond,
                then,
                other,
                pos: _,
            } => {
                writeln!(f, "if {} {:?} else {:?}", cond, then, other)
            }
        }
    }
}

/// implementation of [AstNodeGeneric] for [Stmt]
impl<'a> AstNodeGeneric<'a> for Stmt {
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        let mut res = Issues::ok();

        use self::Stmt::*;
        match self {
            Block { stmts, .. } => {
                for s in stmts {
                    res = res + s.check(st);
                }
            }
            Assert { expr, .. } => {
                res = res + expr.check(st) + expr.match_type(Type::Boolean, st);
            }
            Return { expr, .. } => {
                // TODO: typecheck, lookup return symbol
                res = res + expr.check(st)
            }
            IfElse {
                cond, then, other, ..
            } => {
                res = res + cond.check(st) + cond.match_type(Type::Boolean, st);

                // TODO: type check conditional!

                st.create_context(String::from("if_then"));
                match then.as_ref() {
                    Block { .. } => res = res + then.check(st),
                    _ => panic!("expected a block statement"),
                };
                st.drop_context();

                st.create_context(String::from("if_else"));
                match other.as_ref() {
                    Some(s) => res = res + s.check(st),
                    None => (),
                };
                st.drop_context();
            }
            Let {
                pos,
                typeinfo,
                lhs,
                rhs,
            } => {
                // check the expression and the type info
                res = res + rhs.check(st) + rhs.match_type(*typeinfo, st);

                // add the symbol to the context
                let sym = Symbol::new(
                    lhs.clone(),
                    *typeinfo,
                    SymbolKind::Variable,
                    pos.clone(),
                    AstNode::Statement(self),
                );
                st.insert(sym);
            }
        }

        // return the number of issues found
        res
    }

    fn name(&self) -> &str {
        "Statement"
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        match &self {
            Stmt::IfElse { pos, .. } => pos,
            Stmt::Return { pos, .. } => pos,
            Stmt::Assert { pos, .. } => pos,
            Stmt::Let { pos, .. } => pos,
            Stmt::Block { pos, .. } => pos,
        }
    }
}
