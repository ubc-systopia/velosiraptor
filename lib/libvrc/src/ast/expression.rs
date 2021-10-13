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

///! Ast Module of the Velosiraptor Compiler
use std::fmt;

use crate::ast::{utils, AstNode, Issues, Param, SymbolKind, SymbolTable, Type};
use crate::error::VrsError;
use crate::token::TokenStream;

/// Binary operations for [Expr] <OP> [Expr]
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum BinOp {
    // arithmetic opreators
    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
    LShift,
    RShift,
    And,
    Xor,
    Or,
    // boolean operators
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    Land,
    Lor,
    Implies,
}

/// Implementation of binary operators
impl BinOp {
    /// Evalutes a BinOp expression
    ///
    /// The function creates a new [Expr] from the supplied operation and expression.
    /// It folds the expression if applicapble
    ///
    /// # Example
    ///
    /// `1 + 4 => 5`
    /// `1 < 5 => True`
    /// `x + 5 => x + 5`
    pub fn eval(&self, lhs: Expr, rhs: Expr, pos: TokenStream) -> Expr {
        use BinOp::*;
        use Expr::*;

        match (self, lhs, rhs) {
            // XXX: handle case where v1 + v2 overflows
            (Plus, Number { value: v1, .. }, Number { value: v2, .. }) => Number {
                value: v1 + v2,
                pos,
            },
            // XXX: handle case where v2 > v1
            (Minus, Number { value: v1, .. }, Number { value: v2, .. }) => Number {
                value: v1 - v2,
                pos,
            },
            // XXX: handle case where v1 * v2 overflows
            (Multiply, Number { value: v1, .. }, Number { value: v2, .. }) => Number {
                value: v1 * v2,
                pos,
            },
            // XXX: handle case where v2 == 0
            (Divide, Number { value: v1, .. }, Number { value: v2, .. }) => Number {
                value: v1 / v2,
                pos,
            },
            // XXX: handle case where v2 == 0
            (Modulo, Number { value: v1, .. }, Number { value: v2, .. }) => Number {
                value: v1 % v2,
                pos,
            },
            // XXX: handle case where v2 > 63
            (LShift, Number { value: v1, .. }, Number { value: v2, .. }) => Number {
                value: v1 << v2,
                pos,
            },
            // XXX: handle case where v2 > 63
            (RShift, Number { value: v1, .. }, Number { value: v2, .. }) => Number {
                value: v1 >> v2,
                pos,
            },
            (And, Number { value: v1, .. }, Number { value: v2, .. }) => Number {
                value: v1 & v2,
                pos,
            },
            (Xor, Number { value: v1, .. }, Number { value: v2, .. }) => Number {
                value: v1 ^ v2,
                pos,
            },
            (Or, Number { value: v1, .. }, Number { value: v2, .. }) => Number {
                value: v1 | v2,
                pos,
            },
            // comparisons
            (Eq, Number { value: v1, .. }, Number { value: v2, .. }) => Boolean {
                value: v1 == v2,
                pos,
            },
            (Ne, Number { value: v1, .. }, Number { value: v2, .. }) => Boolean {
                value: v1 != v2,
                pos,
            },
            (Lt, Number { value: v1, .. }, Number { value: v2, .. }) => Boolean {
                value: v1 < v2,
                pos,
            },
            (Gt, Number { value: v1, .. }, Number { value: v2, .. }) => Boolean {
                value: v1 > v2,
                pos,
            },
            (Le, Number { value: v1, .. }, Number { value: v2, .. }) => Boolean {
                value: v1 <= v2,
                pos,
            },
            (Ge, Number { value: v1, .. }, Number { value: v2, .. }) => Boolean {
                value: v1 >= v2,
                pos,
            },
            // booleans
            (Land, Boolean { value: v1, .. }, Boolean { value: v2, .. }) => Boolean {
                value: v1 && v2,
                pos,
            },
            (Lor, Boolean { value: v1, .. }, Boolean { value: v2, .. }) => Boolean {
                value: v1 || v2,
                pos,
            },
            (Eq, Boolean { value: v1, .. }, Boolean { value: v2, .. }) => Boolean {
                value: v1 == v2,
                pos,
            },
            (Ne, Boolean { value: v1, .. }, Boolean { value: v2, .. }) => Boolean {
                value: v1 != v2,
                pos,
            },
            // can't handle this
            (_, lhs, rhs) => BinaryOperation {
                op: *self,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                pos,
            },
        }
    }

    /// the result type of a binary operation
    fn result_numeric(&self) -> bool {
        use BinOp::*;
        match self {
            // arithmetic opreators
            Plus => true,
            Minus => true,
            Multiply => true,
            Divide => true,
            Modulo => true,
            LShift => true,
            RShift => true,
            And => true,
            Xor => true,
            Or => true,
            // boolean operators
            Eq => false,
            Ne => false,
            Lt => false,
            Gt => false,
            Le => false,
            Ge => false,
            Land => false,
            Lor => false,
            Implies => false,
        }
    }

    /// the result type of a binary operation
    fn result_boolean(&self) -> bool {
        use BinOp::*;
        match self {
            // arithmetic opreators
            Plus => false,
            Minus => false,
            Multiply => false,
            Divide => false,
            Modulo => false,
            LShift => false,
            RShift => false,
            And => false,
            Xor => false,
            Or => false,
            // boolean operators
            Eq => true,
            Ne => true,
            Lt => true,
            Gt => true,
            Le => true,
            Ge => true,
            Land => true,
            Lor => true,
            Implies => true,
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, format: &mut fmt::Formatter) -> fmt::Result {
        use self::BinOp::*;
        match self {
            Plus => write!(format, "+"),
            Minus => write!(format, "-"),
            Multiply => write!(format, "*"),
            Divide => write!(format, "/"),
            Modulo => write!(format, "%"),
            LShift => write!(format, "<<"),
            RShift => write!(format, ">>"),
            And => write!(format, "&"),
            Xor => write!(format, "^"),
            Or => write!(format, "|"),
            Eq => write!(format, "=="),
            Ne => write!(format, "!="),
            Lt => write!(format, "<"),
            Gt => write!(format, ">"),
            Le => write!(format, "<="),
            Ge => write!(format, ">="),
            Land => write!(format, "&&"),
            Lor => write!(format, "||"),
            Implies => write!(format, "==>"),
        }
    }
}

/// Represents an unary operator
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum UnOp {
    // arithmetic operators
    Not,
    Ref,
    // boolean operator
    LNot,
}

/// Implementation of an unary operator
impl UnOp {
    pub fn eval(&self, val: Expr, pos: TokenStream) -> Expr {
        use Expr::*;
        use UnOp::*;
        match (self, val) {
            (LNot, Boolean { value, pos: _ }) => Boolean { value: !value, pos },
            (Not, Number { value, pos: _ }) => Number { value: !value, pos },
            (_, val) => UnaryOperation {
                op: *self,
                val: Box::new(val),
                pos,
            },
        }
    }
}

/// Implementation of [fmt::Display] for [UnOp]
impl fmt::Display for UnOp {
    fn fmt(&self, format: &mut fmt::Formatter) -> fmt::Result {
        use self::UnOp::*;
        match self {
            Not => write!(format, "~"),
            LNot => write!(format, "!"),
            Ref => write!(format, "&"),
        }
    }
}

/// representation of a quantifier
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Quantifier {
    Forall,
    Exists,
}
/// Implementation of [fmt::Display] for [Quantifier]
impl fmt::Display for Quantifier {
    fn fmt(&self, format: &mut fmt::Formatter) -> fmt::Result {
        use self::Quantifier::*;
        match self {
            Forall => write!(format, "forall"),
            Exists => write!(format, "exists"),
        }
    }
}

/// Represents an Expression
///
/// The expressions form a trie that is the being evaluated bottom up.
#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    /// Represents an identifier. That may be qualified or not.  `a.b`
    Identifier { path: Vec<String>, pos: TokenStream },
    /// Represents a constant, unsigned number  `5`
    Number { value: u64, pos: TokenStream },
    /// Represents a constant boolean value  `True | False`
    Boolean { value: bool, pos: TokenStream },
    /// Represents a binary operation  `a + 1`
    BinaryOperation {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        pos: TokenStream,
    },
    /// Represents an unary operation `!a`
    UnaryOperation {
        op: UnOp,
        val: Box<Expr>,
        pos: TokenStream,
    },
    /// Represents a function call  `a.b(x,y)`
    FnCall {
        path: Vec<String>,
        args: Vec<Expr>,
        pos: TokenStream,
    },
    /// Represents a slice  `a[1..x]`
    Slice {
        path: Vec<String>,
        slice: Box<Expr>,
        pos: TokenStream,
    },
    /// Represents an element aaccess `a[0]`
    Element {
        path: Vec<String>,
        idx: Box<Expr>,
        pos: TokenStream,
    },
    /// Reprsents a range  `start..end`
    Range {
        start: Box<Expr>,
        end: Box<Expr>,
        pos: TokenStream,
    },
    /// Represents a quantifier `forall x | x > 0`
    Quantifier {
        kind: Quantifier,
        vars: Vec<Param>,
        expr: Box<Expr>,
        pos: TokenStream,
    },
}

/// Implementation of [Expr]
impl Expr {
    /// returns ture if the expression is a constant expression
    ///
    /// it consults the symbol table to figure out whether the symbol / variable is constant
    pub fn is_const_expr(&self, st: &SymbolTable) -> bool {
        use Expr::*;
        match self {
            // numbers and booleans are constant
            Number { .. } => true,
            Boolean { .. } => true,
            // unary and binary operations are constant, if and only if each operand is constnat
            BinaryOperation { lhs, rhs, .. } => lhs.is_const_expr(st) && rhs.is_const_expr(st),
            UnaryOperation { val, .. } => val.is_const_expr(st),
            // an identifyer is constnat, if its in the symbol table as a constant
            Identifier { path, .. } => {
                // TODO: deal with context.symbol
                let name = path.join(".");
                match st.lookup(&name) {
                    Some(s) => s.is_const(),
                    None => false,
                }
            }
            // everything else is not constant
            _ => false,
        }
    }

    /// matches a symbol with a given type
    pub fn match_symbol(path: &[String], pos: &TokenStream, ty: Type, st: &SymbolTable) -> Issues {
        let name = path.join(".");
        match st.lookup(&name) {
            Some(s) => {
                if !ty.compatible(s.typeinfo) {
                    // warning
                    let msg = format!(
                        "expected expression of type `{}`, {} symbol `{}` has type `{}`",
                        ty.to_type_string(),
                        s.kind,
                        name,
                        s.typeinfo.to_type_string()
                    );
                    let hint = String::from("define symbol with matching type");
                    VrsError::new_err(pos, msg, Some(hint)).print();
                    Issues::err()
                } else {
                    Issues::ok()
                }
            }
            None => {
                // warning
                let msg = format!(
                    "expected expression of type `{}`, symbol `{}` was not found",
                    ty.to_type_string(),
                    name
                );
                let hint = format!("define symbol with type `{}`", ty.to_type_string());
                VrsError::new_err(pos, msg, Some(hint)).print();
                Issues::err()
            }
        }
    }

    /// matches the type of the expressin with the supplied type
    pub fn match_type(&self, ty: Type, st: &SymbolTable) -> Issues {
        use Expr::*;
        match self {
            // numbers and booleans are constant
            Number { pos, .. } => {
                if !ty.is_numeric() {
                    // warning
                    let msg = format!(
                        "expected expression of type `{}`, but was of numeric type.`",
                        ty.to_type_string()
                    );
                    let hint = format!("convert to `{}` type.", ty.to_type_string());
                    VrsError::new_err(pos, msg, Some(hint)).print();
                    Issues::err()
                } else {
                    Issues::ok()
                }
            }
            Boolean { pos, .. } => {
                if !ty.is_boolean() {
                    // warning
                    let msg = format!(
                        "expected expression of type `{}`, but was of boolean type.`",
                        ty.to_type_string()
                    );
                    let hint = format!("convert to `{}` type.", ty.to_type_string());
                    VrsError::new_err(pos, msg, Some(hint)).print();
                    Issues::err()
                } else {
                    Issues::ok()
                }
            }
            // unary and binary operations are constant, if and only if each operand is constnat
            BinaryOperation { op, pos, .. } => {
                if op.result_boolean() && ty.is_boolean() || op.result_numeric() && ty.is_numeric()
                {
                    Issues::ok()
                } else {
                    // warning
                    let msg = format!("expected expression of type `{}`", ty.to_type_string(),);
                    let hint = format!(
                        "change expression to produce `{}` or change type",
                        ty.to_type_string()
                    );
                    VrsError::new_err(pos, msg, Some(hint)).print();
                    Issues::err()
                }
            }
            UnaryOperation { val, .. } => val.match_type(ty, st),
            // an identifyer is constnat, if its in the symbol table as a constant
            Identifier { path, pos } => Self::match_symbol(path, pos, ty, st),
            FnCall { path, pos, .. } => Self::match_symbol(path, pos, ty, st),
            Element { path, pos, .. } => Self::match_symbol(path, pos, ty, st),
            Quantifier { pos, .. } => {
                if ty.is_boolean() {
                    Issues::ok()
                } else {
                    let msg = format!(
                        "expected expression of type `{}`, but quantifier is boolean",
                        ty.to_type_string(),
                    );
                    VrsError::new_err(pos, msg, None).print();
                    Issues::err()
                }
            }
            // everything else is currently not supported
            x => {
                // warning
                let msg = format!(
                    "expected expression of type `{}`, but found unsupported exprssion {}",
                    ty.to_type_string(),
                    x
                );
                let hint = format!(
                    "change expression to produce `{}` or change type",
                    ty.to_type_string()
                );
                VrsError::new_err(x.loc(), msg, Some(hint)).print();
                Issues::err()
            }
        }
    }

    /// applies constant folding
    pub fn fold_constants(self) -> Self {
        use Expr::*;
        match self {
            BinaryOperation { op, lhs, rhs, pos } => {
                let lhs = lhs.fold_constants();
                let rhs = rhs.fold_constants();
                op.eval(lhs, rhs, pos)
            }
            UnaryOperation { op, val, pos } => {
                let val = val.fold_constants();
                op.eval(val, pos)
            }
            Slice { path, slice, pos } => {
                let slice = slice.fold_constants();
                Slice {
                    path,
                    slice: Box::new(slice),
                    pos,
                }
            }
            Element { path, idx, pos } => {
                let idx = idx.fold_constants();
                Element {
                    path,
                    idx: Box::new(idx),
                    pos,
                }
            }
            id => id,
        }
    }

    /// checks if a given symbol exists with the path
    fn symbol_exists(
        pos: &TokenStream,
        path: &[String],
        st: &SymbolTable,
        kind: &[SymbolKind],
    ) -> Issues {
        let ident = path.join(".");
        match st.lookup(&ident) {
            Some(s) => {
                if !kind.contains(&s.kind) {
                    // warning
                    let msg = format!(
                        "symbol `{}` exists but has a wrong kind. Expected `{:?}`, was `{:?}`",
                        ident, kind, s.kind
                    );
                    let hint = format!(
                        "define this symbol as {:?}, or converts its use to {:?}",
                        kind, s.kind
                    );
                    VrsError::new_err(pos, msg, Some(hint)).print();
                    Issues::err()
                } else {
                    Issues::ok()
                }
            }
            None => {
                let msg = format!("symbol `{}` does not exist within this context", ident);
                VrsError::new_err(pos, msg, None).print();
                Issues::err()
            }
        }
    }

    /// checks that all symbols are defined in the exprssions
    pub fn check_symbols(&self, st: &mut SymbolTable) -> Issues {
        let varkind = &[
            SymbolKind::Const,
            SymbolKind::Parameter,
            SymbolKind::Variable,
            SymbolKind::State,
        ];
        let fnkind = &[SymbolKind::Function];
        use Expr::*;
        match self {
            Identifier { path, pos } => Expr::symbol_exists(pos, path, st, varkind),
            Number { .. } => Issues::ok(),
            Boolean { .. } => Issues::ok(),
            BinaryOperation { lhs, rhs, .. } => lhs.check_symbols(st) + rhs.check_symbols(st),
            UnaryOperation { val, .. } => val.check_symbols(st),
            FnCall { path, args, pos } => {
                let s = Expr::symbol_exists(pos, path, st, fnkind);
                args.iter().fold(s, |acc, e| e.check_symbols(st) + acc)
            }
            Slice { path, slice, pos } => {
                // currently we can't do foo()[]
                let s = Expr::symbol_exists(pos, path, st, varkind);
                s + slice.check_symbols(st)
            }
            Element { path, idx, pos } => {
                let s = Expr::symbol_exists(pos, path, st, varkind);
                s + idx.check_symbols(st)
            }
            Range { start, end, .. } => start.check_symbols(st) + end.check_symbols(st),
            Quantifier { vars, expr, .. } => {
                let mut issues = Issues::ok();
                // create st context
                st.create_context(String::from("quantifier"));
                issues.inc_err(utils::check_double_entries(vars));
                for v in vars {
                    if let Some(s) = st.lookup(&v.name) {
                        let msg = format!(
                            "identifier `{}` shadows a previously defined symbol",
                            s.name
                        );
                        let hint = String::from("consider giving the variable another name");
                        VrsError::new_warn(v.loc(), msg, Some(hint)).print();
                        issues.inc_warn(1);
                    }
                    issues = issues + utils::check_snake_case(&v.name, v.loc());
                    st.insert(v.to_symbol());
                }

                issues = issues + expr.check_symbols(st) + expr.match_type(Type::Boolean, st);

                // pop systable context
                st.drop_context();

                issues
            }
        }
    }

    /// checks if the types of the expression match
    pub fn check_types(&self, _st: &mut SymbolTable) -> Issues {
        Issues::ok()
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, format: &mut fmt::Formatter) -> fmt::Result {
        use self::Expr::*;
        match self {
            Identifier { path, .. } => write!(format, "{}", path.join(".")),
            Number { value, .. } => write!(format, "{}", value),
            Boolean { value, .. } => write!(format, "{}", value),
            BinaryOperation { op, lhs, rhs, .. } => write!(format, "({} {} {})", lhs, op, rhs),
            UnaryOperation { op, val, .. } => write!(format, "{}({})", op, val),
            FnCall { path, .. } => write!(format, "{}()", path.join(".")),
            Slice { path, slice, .. } => write!(format, "{}[{}]", path.join("."), slice),
            Element { path, idx, .. } => write!(format, "{}[{}]", path.join("."), idx),
            Range { start, end, .. } => write!(format, "{}..{}", start, end),
            Quantifier { kind, expr, .. } => write!(format, "{} {}", kind, expr),
        }
    }
}

impl AstNode for Expr {
    fn name(&self) -> &str {
        "Expression"
    }

    /// performs teh ast check on the expression node
    fn check(&self, st: &mut SymbolTable) -> Issues {
        let mut res = Issues::ok();

        // Check 1: Sybol definitions
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that the symbols are defined
        // Notes:
        // --------------------------------------------------------------------------------------

        res = res + self.check_symbols(st);

        // Check 2: Type checks
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that teh types match
        // Notes:
        // --------------------------------------------------------------------------------------

        res + self.check_types(st)
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        use self::Expr::*;
        match &self {
            Identifier { pos, .. } => pos,
            Number { pos, .. } => pos,
            Boolean { pos, .. } => pos,
            BinaryOperation { pos, .. } => pos,
            UnaryOperation { pos, .. } => pos,
            FnCall { pos, .. } => pos,
            Slice { pos, .. } => pos,
            Element { pos, .. } => pos,
            Range { pos, .. } => pos,
            Quantifier { pos, .. } => pos,
        }
    }
}

#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use crate::parser::expression::{arith_expr, bool_expr};
#[cfg(test)]
use crate::sourcepos::SourcePos;

#[cfg(test)]
macro_rules! parse_equal (
    ($parser:expr, $lhs:expr, $rhs:expr) => (
        let sp = SourcePos::new("stdio", $lhs);
        let tokens = Lexer::lex_source_pos(sp).unwrap();
        let ts = TokenStream::from_vec(tokens);
        let (_, ex) = $parser(ts.clone()).unwrap();
        assert_eq!(
            format!("{}", ex.fold_constants()),
            String::from($rhs)
        );
    )
);

#[test]
fn const_folding_test() {
    parse_equal!(arith_expr, "1+3", "4");
    parse_equal!(arith_expr, "1+3*4", "13");
    parse_equal!(bool_expr, "true && false", "false");
    parse_equal!(bool_expr, "true || false", "true");
    //assert_eq!(ex.map(|(i, x)| (i, format!("{}", x))), String::from("4"));
}
