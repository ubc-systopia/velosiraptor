// Rosette Code Generation - Expressions
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

//! Rosette Expressions

// stdlib
use std::fmt;

/// Represents a constante definition
///
/// # Example
///
/// ; the maximum depth
/// (define maxdepth 5)
///
#[derive(PartialEq, Clone, Debug)]
pub enum RExpr {
    /// #:param
    Param {
        param: String,
    },
    /// (match val-expr clause ...)
    ///     clause = [pat body ...+]
    Match {
        valexpr: String,
        clauses: Vec<(RExpr, Vec<RExpr>)>,
    },
    // a conditional
    Cond {
        test: Box<RExpr>,
        then: Vec<RExpr>,
        other: Vec<RExpr>,
    },
    // bitvector operations
    BVBinOp {
        op: BVOp,
        lhs: Box<RExpr>,
        rhs: Box<RExpr>,
    },
    Not {
        expr: Box<RExpr>,
    },
    // Constant Bitvector Values
    Const {
        width: u8,
        value: u64,
    },
    Let {
        defs: Vec<(String, RExpr)>,
        body: Vec<RExpr>,
        star: bool,
    },
    // a variable
    Variable {
        name: String,
    },
    Text {
        text: String,
    },
    Assert {
        test: Box<RExpr>,
    },
    Assume {
        test: Box<RExpr>,
    },
    FnCall {
        ident: String,
        args: Vec<RExpr>,
    },
    Block {
        expr: Vec<(String, RExpr)>,
    },
    Begin {
        exprs: Vec<RExpr>,
    },
    Comment {
        comment: String,
    },
}
#[derive(PartialEq, Clone, Copy, Debug)]
pub enum BVOp {
    BVAnd,
    BVOr,
    BVShr,
    BVShl,
    BVEq,
    BVAdd,
    BVSub,
    BVLt,
    BVLe,
    BVGt,
    BVGe,
}

impl BVOp {
    /// formats corresponding rosette code
    pub fn to_code(&self) -> &str {
        match *self {
            BVOp::BVShl => "bvshl",
            BVOp::BVEq => "bveq",
            BVOp::BVAnd => "bvand",
            BVOp::BVOr => "bvor",
            BVOp::BVShr => "bvlshr",
            BVOp::BVAdd => "bvadd",
            BVOp::BVSub => "bvsub",
            BVOp::BVLt => "bvult",
            BVOp::BVLe => "bvule",
            BVOp::BVGt => "bvugt",
            BVOp::BVGe => "bvuge",
        }
    }
}

impl fmt::Display for BVOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let opstr = match *self {
            BVOp::BVShl => "<",
            BVOp::BVEq => "=",
            BVOp::BVAnd => "&",
            BVOp::BVOr => "|",
            BVOp::BVShr => ">",
            BVOp::BVAdd => "+",
            BVOp::BVSub => "-",
            BVOp::BVLt => "<",
            BVOp::BVLe => "<=",
            BVOp::BVGt => ">",
            BVOp::BVGe => ">=",
        };

        write!(f, "{}", opstr)
    }
}

impl RExpr {
    pub fn constraint(var: String, op: BVOp, value: u64) -> RExpr {
        println!("adding constraint: {} {} {}", var, op, value);
        RExpr::assume(RExpr::BVBinOp {
            op,
            lhs: Box::new(RExpr::var(var)),
            rhs: Box::new(RExpr::num(64, value)),
        })
    }

    pub fn param(param: String) -> Self {
        RExpr::Param { param }
    }
    pub fn var(name: String) -> Self {
        RExpr::Variable { name }
    }
    pub fn num(width: u8, value: u64) -> Self {
        // TODO: check that this makes sense
        RExpr::Const { width, value }
    }

    pub fn comment(comment: String) -> Self {
        RExpr::Comment { comment }
    }

    pub fn neq(expr: RExpr) -> Self {
        RExpr::Not {
            expr: Box::new(expr),
        }
    }

    pub fn text(text: String) -> Self {
        RExpr::Text { text }
    }
    pub fn bveq(lhs: RExpr, rhs: RExpr) -> Self {
        RExpr::BVBinOp {
            op: BVOp::BVEq,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }
    pub fn bvne(lhs: RExpr, rhs: RExpr) -> Self {
        RExpr::neq(RExpr::BVBinOp {
            op: BVOp::BVEq,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        })
    }
    pub fn bvlt(lhs: RExpr, rhs: RExpr) -> Self {
        RExpr::BVBinOp {
            op: BVOp::BVLt,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }
    pub fn bvle(lhs: RExpr, rhs: RExpr) -> Self {
        RExpr::BVBinOp {
            op: BVOp::BVLe,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }
    pub fn bvgt(lhs: RExpr, rhs: RExpr) -> Self {
        RExpr::BVBinOp {
            op: BVOp::BVGt,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }
    pub fn bvge(lhs: RExpr, rhs: RExpr) -> Self {
        RExpr::BVBinOp {
            op: BVOp::BVGe,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }
    pub fn bvadd(lhs: RExpr, rhs: RExpr) -> Self {
        RExpr::BVBinOp {
            op: BVOp::BVAdd,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }
    pub fn bvsub(lhs: RExpr, rhs: RExpr) -> Self {
        RExpr::BVBinOp {
            op: BVOp::BVSub,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }
    pub fn bvand(lhs: RExpr, rhs: RExpr) -> Self {
        RExpr::BVBinOp {
            op: BVOp::BVAnd,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }
    pub fn bvor(lhs: RExpr, rhs: RExpr) -> Self {
        RExpr::BVBinOp {
            op: BVOp::BVOr,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }
    pub fn bvshr(val: RExpr, amount: RExpr) -> Self {
        RExpr::BVBinOp {
            op: BVOp::BVShr,
            lhs: Box::new(val),
            rhs: Box::new(amount),
        }
    }
    pub fn bvshl(val: RExpr, amount: RExpr) -> Self {
        RExpr::BVBinOp {
            op: BVOp::BVShl,
            lhs: Box::new(val),
            rhs: Box::new(amount),
        }
    }

    pub fn fncall(ident: String, args: Vec<RExpr>) -> Self {
        RExpr::FnCall { ident, args }
    }
    pub fn block(expr: Vec<(String, RExpr)>) -> Self {
        RExpr::Block { expr }
    }
    pub fn matchexpr(valexpr: String, clauses: Vec<(RExpr, Vec<RExpr>)>) -> Self {
        RExpr::Match { valexpr, clauses }
    }
    pub fn letexpr(defs: Vec<(String, RExpr)>, body: Vec<RExpr>) -> Self {
        RExpr::Let {
            defs,
            body,
            star: false,
        }
    }
    pub fn letstart(defs: Vec<(String, RExpr)>, body: Vec<RExpr>) -> Self {
        RExpr::Let {
            defs,
            body,
            star: true,
        }
    }
    pub fn assert(expr: RExpr) -> Self {
        RExpr::Assert {
            test: Box::new(expr),
        }
    }
    pub fn assume(expr: RExpr) -> Self {
        RExpr::Assume {
            test: Box::new(expr),
        }
    }
    pub fn begin(exprs: Vec<RExpr>) -> Self {
        RExpr::Begin { exprs }
    }

    /// formats corresponding rosette code
    pub fn to_code(&self, indent: usize) -> String {
        let istr = " ".repeat(indent);
        use RExpr::*;
        match self {
            Variable { name } => format!("{}{}", istr, name),
            Comment { comment } => format!("{}; {}\n", istr, comment),
            Text { text } => format!("{}\"{}\"", istr, text),
            Const { value, .. } => format!("{}(int #x{:x})", istr, value),
            Not { expr } => format!("{}(not\n {})", istr, expr.to_code(indent + 2)),
            BVBinOp { op, lhs, rhs } => format!(
                "{}({}\n{}\n{}\n{})",
                istr,
                op.to_code(),
                lhs.to_code(indent + 2),
                rhs.to_code(indent + 2),
                istr
            ),
            FnCall { ident, args } => {
                if args.is_empty() {
                    format!("{}({})", istr, ident)
                } else {
                    let args = args
                        .iter()
                        .map(|a| a.to_code(indent + 2))
                        .collect::<Vec<String>>();
                    format!("{}({}\n{}\n{})", istr, ident, args.join("\n"), istr)
                }
            }
            Block { expr } => {
                let args = expr
                    .iter()
                    .map(|(i, e)| format!("{}  {}\n{}", istr, i, e.to_code(indent + 2)))
                    .collect::<Vec<String>>();
                format!("{}[\n{}\n{}]", istr, args.join(" "), istr)
            }
            Match { valexpr, clauses } => {
                let clauses = clauses
                    .iter()
                    .map(|(i, c)| {
                        let e = c
                            .iter()
                            .map(|e| e.to_code(indent + 4))
                            .collect::<Vec<String>>();
                        format!(
                            "  {}[\n{}\n{}\n{}  ] ",
                            istr,
                            i.to_code(indent + 4),
                            e.join("\n"),
                            istr
                        )
                    })
                    .collect::<Vec<String>>();
                format!(
                    "{}(match {}\n{}\n{})\n",
                    istr,
                    valexpr,
                    clauses.join("\n"),
                    istr
                )
            }
            Assume { test } => {
                format!("{}(assume\n{}\n{})\n", istr, test.to_code(indent + 2), istr)
            }
            Assert { test } => {
                format!("{}(assert\n{}\n{})\n", istr, test.to_code(indent + 2), istr)
            }
            Begin { exprs } => {
                let mut s = String::new();
                for e in exprs {
                    s.push_str(&format!("{}{}", istr, e.to_code(indent)));
                }
                s
            }
            // defs: Vec<(String, RExpr)>,
            // body: Vec<RExpr>,
            Let { defs, body, star } => {
                let d = defs
                    .iter()
                    .map(|(d, e)| {
                        format!(
                            "{}    [ {}\n{}\n{}    ]",
                            istr,
                            d,
                            e.to_code(indent + 6),
                            istr
                        )
                    })
                    .collect::<Vec<String>>();
                let e = body
                    .iter()
                    .map(|e| e.to_code(indent + 2))
                    .collect::<Vec<String>>();
                let s = if *star { "*" } else { "" };
                format!(
                    "{}(let{} (\n{}\n{}  )\n{}\n{})",
                    istr,
                    s,
                    d.join("\n"),
                    istr,
                    e.join("\n"),
                    istr,
                )
            }
            Param { param } => format!("{}#:{}", istr, param),
            x => format!("UNKNOWN! {:?}\n", x),
        }
    }
}
