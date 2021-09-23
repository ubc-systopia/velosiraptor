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

///! Statement module
// std lib imports
use std::fmt;

// library internal imports
use crate::ast::{AstNode, Expr, Issues, Symbol, SymbolKind, SymbolTable, Type};
use crate::token::TokenStream;

/// Represents a statement
#[derive(Debug, PartialEq, Clone)]
pub enum Stmt {
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
        then: Vec<Stmt>,
        other: Vec<Stmt>,
    },
    /// return statement
    Return { pos: TokenStream, expr: Expr },
    /// assert statement
    Assert { pos: TokenStream, expr: Expr },
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Stmt::*;
        match self {
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

/// implementation of [AstNode] for [Field]
impl AstNode for Stmt {
    fn check(&self, st: &mut SymbolTable) -> Issues {
        let mut res = Issues::ok();

        use self::Stmt::*;
        match self {
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
                for s in then {
                    res = res + s.check(st);
                }
                st.drop_context();

                st.create_context(String::from("if_else"));
                for s in other {
                    res = res + s.check(st);
                }
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
                let sym = Symbol::new(lhs.clone(), *typeinfo, SymbolKind::Variable, pos.clone());
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
        }
    }
}
