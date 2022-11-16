// Velosiraptor Code Generator
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

//! Synthesis Module: Smt2 Expressions

use smt2::{SortedVar, Term};

use velosiast::ast::{
    VelosiAstBinOp, VelosiAstExpr, VelosiAstParam, VelosiAstQuantifier, VelosiAstUnOp,
};

use super::flags::flags_get_fn_name;
use super::model::{
    model_field_get_fn_name, model_field_set_fn_name, model_slice_get_fn_name,
    model_slice_set_fn_name,
};

pub fn p2p(i: &str) -> &str {
    match i {
        "state" => "State",
        "interface" => "IFace",
        i => i, // _ => panic!("uknown case: {}", i),
    }
}

pub fn param_to_sortedvar(p: &VelosiAstParam) -> SortedVar {
    let name = p.ident_to_string();
    let sort = super::types::type_to_smt2(&p.ptype);
    SortedVar::new(name, sort)
}

pub fn flags_get_fn(var: &str, flag: &str) -> Term {
    let ident = flags_get_fn_name(flag);
    Term::fn_apply(ident, vec![Term::ident(var.to_string())])
}

pub fn model_accessor_read_fn(stvar: &str, part: &str, fieldslice: &str) -> Term {
    let ident = model_field_get_fn_name(p2p(part), fieldslice);
    smt2::Term::fn_apply(ident, vec![Term::ident(stvar.to_string())])
}

pub fn model_accessor_write_fn(stvar: &str, part: &str, fieldslice: &str) -> Term {
    let ident = model_field_set_fn_name(p2p(part), fieldslice);
    smt2::Term::fn_apply(ident, vec![Term::ident(stvar.to_string())])
}

pub fn model_slice_accessor_read_fn(stvar: &str, part: &str, field: &str, slice: &str) -> Term {
    let ident = model_slice_get_fn_name(p2p(part), field, slice);
    smt2::Term::fn_apply(ident, vec![Term::ident(stvar.to_string())])
}

pub fn model_slice_accessor_write_fn(stvar: &str, part: &str, field: &str, slice: &str) -> Term {
    let ident = model_slice_set_fn_name(p2p(part), field, slice);
    smt2::Term::fn_apply(ident, vec![Term::ident(stvar.to_string())])
}

/// Convert a
pub fn expr_to_smt2(e: &VelosiAstExpr, stvar: &str) -> smt2::Term {
    use VelosiAstExpr::*;
    match e {
        IdentLiteral(i) => {
            if i.path.len() == 1 {
                Term::ident(i.path[0].to_string())
            } else if i.path.len() == 2 {
                // if we have flags, then this is bascially a field access
                if i.etype.is_flags() {
                    flags_get_fn(i.path[0].as_str(), i.path[1].as_str())
                } else {
                    model_accessor_read_fn(stvar, i.path[0].as_str(), i.path[1].as_str())
                }
            } else if i.path.len() == 3 {
                //let fieldslice = format!("{}.{}", i.path[1], i.path[2]);
                model_slice_accessor_read_fn(
                    stvar,
                    i.path[0].as_str(),
                    i.path[1].as_str(),
                    i.path[2].as_str(),
                )
            } else {
                unreachable!("path of unexpected length: {:?}", i.path);
            }
        }
        NumLiteral(i) => Term::num(i.val),
        BoolLiteral(i) => Term::binary(i.val),
        BinOp(i) => {
            use VelosiAstBinOp::*;
            let lhs = expr_to_smt2(i.lhs.as_ref(), stvar);
            let rhs = expr_to_smt2(i.rhs.as_ref(), stvar);
            match i.op {
                // arithmetic opreators
                Plus => Term::bvadd(lhs, rhs),
                Minus => Term::bvsub(lhs, rhs),
                Multiply => Term::bvmul(lhs, rhs),
                Divide => Term::bvdiv(lhs, rhs),
                Modulo => unimplemented!("handling of modulo operator"),
                LShift => Term::bvshl(lhs, rhs),
                RShift => Term::bvshr(lhs, rhs),
                And => Term::bvand(lhs, rhs),
                Xor => Term::bvxor(lhs, rhs),
                Or => Term::bvor(lhs, rhs),
                // boolean operators
                Eq => Term::bveq(lhs, rhs),
                Ne => Term::bvne(lhs, rhs),
                Lt => Term::bvlt(lhs, rhs),
                Gt => Term::bvgt(lhs, rhs),
                Le => Term::bvle(lhs, rhs),
                Ge => Term::bvge(lhs, rhs),
                Land => Term::land(lhs, rhs),
                Lor => Term::lor(lhs, rhs),
                Implies => lhs.implies(rhs),
            }
        }
        UnOp(i) => {
            use VelosiAstUnOp::*;
            let expr = expr_to_smt2(i.expr.as_ref(), stvar);
            match i.op {
                Not => Term::bvnot(expr),
                LNot => Term::lnot(expr),
            }
        }
        Quantifier(i) => {
            use VelosiAstQuantifier::*;
            let expr = expr_to_smt2(i.expr.as_ref(), stvar);
            let vars = i
                .params
                .iter()
                .map(|p| param_to_sortedvar(p.as_ref()))
                .collect();
            match i.quant {
                Forall => Term::forall(vars, expr),
                Exists => Term::exists(vars, expr),
            }
        }
        FnCall(i) => {
            let mut args = vec![Term::ident(stvar.to_string())];
            args.extend(i.args.iter().map(|a| expr_to_smt2(a, stvar)));
            Term::fn_apply(i.name.to_string(), args)
        }
        IfElse(i) => Term::ifelse(
            expr_to_smt2(i.cond.as_ref(), stvar),
            expr_to_smt2(i.then.as_ref(), stvar),
            expr_to_smt2(i.other.as_ref(), stvar),
        ),
        Slice(_i) => unimplemented!("handling of slice expressions"),
        Range(_i) => unimplemented!("handling of range expressions"),
    }
}
