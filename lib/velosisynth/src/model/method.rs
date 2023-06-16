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

//! State Synthesis Module: Rosette

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

// rosette language library imports
use smt2::{Function, Smt2Context, SortedVar, Term};

// crate imports
use super::{expr, types};
use velosiast::ast::{VelosiAstBinOp, VelosiAstExpr, VelosiAstMethod, VelosiAstParam};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Function Names
////////////////////////////////////////////////////////////////////////////////////////////////////

pub fn valid_map_result_name(idx: Option<usize>) -> String {
    if let Some(i) = idx {
        format!("valid.map.result.{i}")
    } else {
        "valid.map.result".to_string()
    }
}

pub fn valid_unmap_result_name(idx: Option<usize>) -> String {
    if let Some(i) = idx {
        format!("valid.unmap.result.{i}")
    } else {
        "valid.unmap.result".to_string()
    }
}

pub fn valid_protect_result_name(idx: Option<usize>) -> String {
    if let Some(i) = idx {
        format!("valid.protect.result.{i}")
    } else {
        "valid.protect.result".to_string()
    }
}

pub fn translate_range_name(idx: Option<usize>) -> String {
    if let Some(i) = idx {
        format!("translate.range.{i}")
    } else {
        "translate.range".to_string()
    }
}

pub fn translate_map_result_name(idx: Option<usize>) -> String {
    if let Some(i) = idx {
        format!("translate.map.result.{i}")
    } else {
        "translate.map.result".to_string()
    }
}

pub fn translate_protect_result_name(idx: Option<usize>) -> String {
    if let Some(i) = idx {
        format!("translate.protect.result.{i}")
    } else {
        "translate.protect.result".to_string()
    }
}

pub fn matchflags_map_result_name(idx: Option<usize>) -> String {
    if let Some(i) = idx {
        format!("matchflags.map.result.{i}")
    } else {
        "matchflags.map.result".to_string()
    }
}

pub fn matchflags_unmap_result_name(idx: Option<usize>) -> String {
    if let Some(i) = idx {
        format!("matchflags.unmap.result.{i}")
    } else {
        "matchflags.unmap.result".to_string()
    }
}

pub fn matchflags_protect_result_name(idx: Option<usize>) -> String {
    if let Some(i) = idx {
        format!("matchflags.protect.result.{i}")
    } else {
        "matchflags.protect.result".to_string()
    }
}

pub fn method_precond_name(mname: &str) -> String {
    format!("{mname}.pre")
}

pub fn method_precond_i_name(mname: &str, i: usize) -> String {
    format!("{mname}.pre.{i}")
}

pub fn method_part_i_name(mname: &str, i: usize) -> String {
    format!("{mname}.part.{i}")
}

pub fn method_assms_name(mname: &str) -> String {
    format!("{mname}.assms")
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Boolean Method Parts
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_bool_method_parts(smt: &mut Smt2Context, method: &VelosiAstMethod) -> usize {
    if let Some(body) = &method.body {
        let parts = body.split_cnf();
        for (i, pre) in parts
            .iter()
            .filter(|p| p.has_state_references())
            .enumerate()
        {
            let name = method_part_i_name(method.ident(), i);
            let mut f = Function::new(name, types::boolean());
            f.add_comment(format!(
                "Function Body part {}: {}, {}",
                i,
                method.ident(),
                method.loc.loc()
            ));

            f.add_arg(String::from("st!0"), types::model());
            for a in method.params.iter() {
                f.add_arg(a.ident_to_string(), types::type_to_smt2(&a.ptype));
            }

            f.add_body(expr::expr_to_smt2(pre, "st!0"));
            smt.function(f);
        }
        parts.len()
    } else {
        0
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Functino Pre Conditions
////////////////////////////////////////////////////////////////////////////////////////////////////

// three types of pre-conditions:
//   - pure state ref:      state.length.present == 1;
//        -> get translated into pre-conditions that must be satisfied
//   - pure arg ref:        va >= 0;
//        -> get translated into assumptions
//   - mixed arg/state ref: va < (state.length.bytes << 4);
//        -> gets extracted into separate method to be checked.

fn add_method_preconditions(smt: &mut Smt2Context, method: &VelosiAstMethod) {
    // ---------------------------------------------------------------------------------------------
    // Adding Individual Function Pre-Conditions
    // ---------------------------------------------------------------------------------------------

    // get the method params as a hashset
    let mut params = HashSet::new();
    for p in method.params.iter() {
        params.insert(p.ident().as_str());
    }

    for (i, pre) in method.requires.iter().enumerate() {
        let name = method_precond_i_name(method.ident(), i);
        let mut f = Function::new(name, types::boolean());

        f.add_arg(String::from("st!0"), types::model());
        for a in method.params.iter() {
            f.add_arg(a.ident_to_string(), types::type_to_smt2(&a.ptype));
        }

        let body = if !pre.has_state_references() {
            // if it has no state references, then we simply add a true body as this is
            // an assumption

            f.add_comment(format!(
                "Function Preconditions part {} (is pure arg ref --> assm): {}, {}",
                i,
                method.ident(),
                method.loc.loc()
            ));

            smt2::Term::binary(true)
        } else if pre.has_var_references(&params) {
            f.add_comment(format!(
                "Function Preconditions part {} (is mixed state/arg ref --> handled separately): {}, {}",
                i,
                method.ident(),
                method.loc.loc()
            ));

            smt2::Term::binary(true)
        } else {
            f.add_comment(format!(
                "Function Preconditions part {} (pure state ref): {}, {}",
                i,
                method.ident(),
                method.loc.loc()
            ));
            expr::expr_to_smt2(pre, "st!0")
        };

        f.add_body(body);
        smt.function(f);
    }

    // ---------------------------------------------------------------------------------------------
    // Adding a Combined Function Pre-Condition
    // ---------------------------------------------------------------------------------------------

    let name = method_precond_name(method.ident());
    let mut f = Function::new(name, types::boolean());
    f.add_comment(format!(
        "Function Preconditions: {}, {}",
        method.ident(),
        method.loc.loc()
    ));

    f.add_arg(String::from("st!0"), types::model());
    for a in method.params.iter() {
        f.add_arg(a.ident_to_string(), types::type_to_smt2(&a.ptype));
    }

    // construct the body of the comined function with pure state references
    let expr = Term::Binary(true);
    let expr = method
        .requires
        .iter()
        .filter(|p| p.has_state_references() && !p.has_var_references(&params))
        .fold(expr, |e, p| Term::land(e, expr::expr_to_smt2(p, "st!0")));

    f.add_body(expr);
    smt.function(f);
}

fn add_method_assms(smt: &mut Smt2Context, method: &VelosiAstMethod) {
    // add the assumptions on the function parameters
    // this includes only pre-conditions that do not have state references
    let name = method_assms_name(method.ident());
    let mut f = Function::new(name, types::boolean());
    f.add_comment(format!(
        "Function Assumptions: {}, {}",
        method.ident(),
        method.loc.loc()
    ));

    f.add_arg(String::from("st!0"), types::model());
    for a in method.params.iter() {
        f.add_arg(a.ident_to_string(), types::type_to_smt2(&a.ptype));
    }

    // add the type constraints on the function parameters
    let a = method.params.iter().fold(Term::Binary(true), |e, a| {
        Term::land(e, types::type_to_assms_fn(&a.ptype, a.ident_to_string()))
    });

    // get all expressions from the pre-condtion that do not have state references,
    // those should be pure assumptions
    let mut expr = method
        .requires
        .iter()
        .filter(|p| !p.has_state_references())
        .fold(a, |e, p| Term::land(e, expr::expr_to_smt2(p, "st!0")));

    if let "matchflags" | "translate" = method.ident.as_str() {
        expr = Term::land(
            expr,
            Term::fn_apply("valid".to_string(), vec![Term::from("st!0")]),
        )
    }

    f.add_body(expr);

    smt.function(f);
}

/// adds methods defined in the unit to the current context
pub fn add_methods(
    smt: &mut Smt2Context,
    methods: Box<dyn Iterator<Item = &Rc<VelosiAstMethod>> + '_>,
) {
    smt.section(String::from("Methods"));

    for m in methods {
        // -----------------------------------------------------------------------------------------
        // Define the Function
        // -----------------------------------------------------------------------------------------

        if let Some(body) = &m.body {
            // TODO: should we add an assert here with pattern?
            let mut f = Function::new(m.ident_to_string(), types::type_to_smt2(&m.rtype));
            f.add_comment(format!("Function: {}, {}", m.ident(), m.loc.loc()));

            f.add_arg(String::from("st"), types::model());
            for a in m.params.iter() {
                f.add_arg(a.ident_to_string(), types::type_to_smt2(&a.ptype));
            }

            f.add_body(expr::expr_to_smt2(body, "st"));
            smt.function(f);

            match m.path().as_str() {
                "valid" => {
                    assert!(m.rtype.is_boolean());
                    let nparts = add_bool_method_parts(smt, m);
                    add_valid_result_checks(smt, nparts);
                }
                "matchflags" => {
                    // if we have match flags we create one for reach element of the
                    assert!(m.rtype.is_boolean());
                    let nparts = add_bool_method_parts(smt, m);
                    add_matchflags_result_checks(smt, nparts);
                }
                "translate" => {
                    add_translate_result_checks(smt);
                    add_translate_range_checks(smt, m.as_ref());
                }
                _ => (),
            }
        } else {
            smt.comment(format!("skipping method {}, no body defined", m.ident()));
        }

        // -----------------------------------------------------------------------------------------
        // Adding Function Pre-conditions on the state, and assumptions on the methods
        // -----------------------------------------------------------------------------------------

        add_method_preconditions(smt, m.as_ref());
        add_method_assms(smt, m.as_ref());
    }
}

pub fn add_valid_result_checks(smt: &mut Smt2Context, nparts: usize) {
    // ---------------------------------------------------------------------------------------------
    // Result when mapping
    // ---------------------------------------------------------------------------------------------

    let map = |smt: &mut Smt2Context, idx| {
        let mut f = Function::new(valid_map_result_name(idx), types::boolean());
        f.add_comment("Checking the valid function result".to_string());

        f.add_arg(String::from("st!0"), types::model());
        f.add_arg(String::from("va"), types::vaddr());
        f.add_arg(String::from("sz"), types::size());
        f.add_arg(String::from("flgs"), types::flags());
        f.add_arg(String::from("pa"), types::paddr());

        let name = if let Some(i) = idx {
            method_part_i_name("valid", i)
        } else {
            "valid".to_string()
        };

        let body = Term::fn_apply(name, vec![Term::from("st!0")]);
        f.add_body(body);
        smt.function(f);
    };

    for i in 0..nparts {
        map(smt, Some(i));
    }
    map(smt, None);

    // ---------------------------------------------------------------------------------------------
    // Result when unmapping
    // ---------------------------------------------------------------------------------------------

    let unmap = |smt: &mut Smt2Context, idx| {
        let mut f = Function::new(valid_unmap_result_name(idx), types::boolean());
        f.add_comment("Checking the valid function result".to_string());

        f.add_arg(String::from("st!0"), types::model());
        f.add_arg(String::from("va"), types::vaddr());
        f.add_arg(String::from("sz"), types::size());

        let name = if let Some(i) = idx {
            method_part_i_name("valid", i)
        } else {
            "valid".to_string()
        };

        let body = Term::fn_apply(name, vec![Term::from("st!0")]);
        f.add_body(body);
        smt.function(f);
    };

    for i in 0..nparts {
        unmap(smt, Some(i));
    }
    unmap(smt, None);

    // ---------------------------------------------------------------------------------------------
    // Result when protecting
    // ---------------------------------------------------------------------------------------------

    let protect = |smt: &mut Smt2Context, idx| {
        let mut f = Function::new(valid_protect_result_name(idx), types::boolean());
        f.add_comment("Checking the valid function result".to_string());

        f.add_arg(String::from("st!0"), types::model());
        f.add_arg(String::from("st!1"), types::model());
        f.add_arg(String::from("va"), types::vaddr());
        f.add_arg(String::from("sz"), types::size());
        f.add_arg(String::from("flgs"), types::flags());

        let name = if let Some(i) = idx {
            method_part_i_name("valid", i)
        } else {
            "valid".to_string()
        };

        let body = Term::eq(
            Term::fn_apply(name.clone(), vec![Term::from("st!0")]),
            Term::fn_apply(name, vec![Term::from("st!1")]),
        );

        f.add_body(body);
        smt.function(f);
    };

    for i in 0..nparts {
        protect(smt, Some(i));
    }
    protect(smt, None);
}

// the range checks are only for the translate function, it checks whether the
// given virtual address would translate
pub fn add_translate_range_checks(smt: &mut Smt2Context, method: &VelosiAstMethod) {
    // basically: forall i : vaddr_t ::
    //  &&  i < va ==> !does_translate(st, i)
    //  &&  va <= i < va + size ==> translate_result(st, va)
    //  &&  i >= va + size ==> !does_translate(st, i)

    let mut vars = HashSet::new();
    vars.insert("va");

    let mut conds = Vec::new();

    for (i, pre) in method.requires.iter().enumerate() {
        if !pre.has_state_references() || !pre.has_var_references(&vars) {
            continue;
        }

        // we do have a mixed pre-condition here, get the binop out

        let binop = if let VelosiAstExpr::BinOp(pre) = pre.as_ref() {
            pre
        } else {
            panic!("expected a binary operation");
        };

        // figure out whether we have a upper bound or a lower bound
        let (_var, _stref, lower_bound) = if binop.lhs.has_var_references(&method.get_param_names())
        {
            // lhs is the var, so if we have a > or >= then this is the lower bound
            (
                &binop.lhs,
                &binop.rhs,
                matches!(binop.op, VelosiAstBinOp::Gt | VelosiAstBinOp::Ge),
            )
        } else {
            // rhs is the var, so if we have a < or <= then this is the lower bound
            (
                &binop.rhs,
                &binop.lhs,
                matches!(binop.op, VelosiAstBinOp::Lt | VelosiAstBinOp::Le),
            )
        };

        // the var string for the forall variable, we use va here otherwise we need to rewrite the
        // precondition expression
        let varstr = "va".to_string();

        let (expr, comment) = if lower_bound {
            // we have something of the for `expr < var` or `expr <= var`
            // forall i. (i < va <==> !pre) && (va <= i <==> pri)

            // forall i. pri == (va <= i)

            (
                Term::bvge(Term::ident(varstr.clone()), Term::ident("va!".to_string()))
                    .eq(expr::expr_to_smt2(pre, "st!0")),
                "forall i. pri == (va <= i)",
            )
        } else {
            // we have something of the for `expr > var` or `expr >= var`
            // forall i. (i < va + sz ==> pre) && (i >= va + sz ==> !pre)
            // forall i. pre == i < va + sz
            (
                Term::bvlt(
                    Term::ident(varstr.clone()),
                    Term::bvadd(
                        Term::ident("va!".to_string()),
                        Term::ident("sz".to_string()),
                    ),
                )
                .eq(expr::expr_to_smt2(pre, "st!0")),
                "forall i. pri == (i < va + size)",
            )
        };

        let mut f = Function::new(translate_range_name(Some(i)), types::boolean());
        f.add_comment("Checking the translate range".to_string());
        f.add_comment(comment.to_string());

        f.add_arg(String::from("st!0"), types::model());
        f.add_arg(String::from("va"), types::vaddr());
        f.add_arg(String::from("va!"), types::vaddr());
        f.add_arg(String::from("sz"), types::size());
        f.add_arg(String::from("flgs"), types::flags());
        f.add_arg(String::from("pa!"), types::paddr());

        // let forallvars = vec![SortedVar::new(varstr.clone(), types::vaddr())];

        // let varconstraints = Term::fn_apply(
        //     "VAddr_t.assms".to_string(),
        //     vec![Term::ident(varstr.clone())],
        // );

        // let body = Term::forall(forallvars, varconstraints.implies(expr));
        // f.add_body(body);
        f.add_body(expr);

        smt.function(f);

        conds.push(pre);
    }

    // ---------------------------------------------------------------------------------------------
    // Adding a Combined Function Pre-Condition
    // ---------------------------------------------------------------------------------------------

    let name = translate_range_name(None);
    let mut f = Function::new(name, types::boolean());
    f.add_comment(format!(
        "Function Semantic Preconditions: {}, {}",
        method.ident(),
        method.loc.loc()
    ));

    f.add_arg(String::from("st!0"), types::model());
    f.add_arg(String::from("va"), types::vaddr());
    f.add_arg(String::from("va!"), types::vaddr());
    f.add_arg(String::from("sz"), types::size());
    f.add_arg(String::from("flgs"), types::flags());
    f.add_arg(String::from("pa!"), types::paddr());

    let expr = Term::Binary(true);

    let expr = method
        .requires
        .iter()
        .filter(|p| p.has_state_references() && p.has_var_references(&vars))
        .fold(expr, |e, p| Term::land(e, expr::expr_to_smt2(p, "st!0")));

    // the var string for the forall variable, we use va here otherwise we need to rewrite the
    // precondition expression
    let varstr = "va".to_string();
    let forallvars = vec![SortedVar::new(varstr.clone(), types::vaddr())];

    let body = Term::land(
        Term::land(
            // i < va ==> !(pre)
            Term::bvlt(Term::ident(varstr.clone()), Term::ident("va!".to_string()))
                .implies(Term::lnot(expr.clone())),
            // i >= va + size ==> !(pre)
            Term::bvge(
                Term::ident(varstr.clone()),
                Term::bvadd(
                    Term::ident("va!".to_string()),
                    Term::ident("sz".to_string()),
                ),
            )
            .implies(Term::lnot(expr.clone())),
        ),
        Term::land(
            Term::bvge(
                Term::ident(varstr.clone()),
                Term::bvadd(
                    Term::ident("va!".to_string()),
                    Term::ident("sz".to_string()),
                ),
            ),
            Term::bvlt(
                Term::ident(varstr),
                Term::bvadd(
                    Term::ident("va!".to_string()),
                    Term::ident("sz".to_string()),
                ),
            ),
        )
        .implies(expr),
    );

    f.add_body(Term::forall(forallvars, body));
    smt.function(f);
}

pub fn add_translate_result_checks(smt: &mut Smt2Context) {
    // basically: forall i : vaddr_t ::
    //  &&  i < va ==> !does_translate(st, i)
    //  &&  va <= i < va + size ==> translate_result(st, va)
    //  &&  i >= va + size ==> !does_translate(st, i)

    // ---------------------------------------------------------------------------------------------
    // Result when mapping
    // ---------------------------------------------------------------------------------------------

    let mut f = Function::new(translate_map_result_name(None), types::boolean());
    f.add_comment("Checking the translate function result".to_string());

    f.add_arg(String::from("st!0"), types::model());
    f.add_arg(String::from("va"), types::vaddr());
    f.add_arg(String::from("sz"), types::size());
    f.add_arg(String::from("flgs"), types::flags());
    f.add_arg(String::from("pa"), types::paddr());

    let varstr = "i!0".to_string();
    let forallvars = vec![SortedVar::new(varstr.clone(), types::size())];

    // forall i | 0 <= i < size :: translate (st!0, va + i) == pa + i
    // forall i :: 0 <= i < size ==> translate (st!0, va + i) == pa + i
    let constr = Term::land(
        Term::bvge(Term::num(0), Term::ident(varstr.clone())),
        Term::bvlt(Term::ident(varstr.clone()), Term::ident("sz".to_string())),
    );

    // translate (st!0, va + i) == pa + i
    let check = Term::bveq(
        Term::fn_apply(
            "translate".to_string(),
            vec![
                Term::ident(String::from("st!0")),
                Term::bvadd(Term::ident("va".to_string()), Term::ident(varstr.clone())),
            ],
        ),
        Term::bvadd(Term::ident(String::from("pa")), Term::ident(varstr)),
    );

    let body = Term::forall(forallvars, constr.implies(check));
    f.add_body(body);
    smt.function(f);

    // ---------------------------------------------------------------------------------------------
    // Result when protecting
    // ---------------------------------------------------------------------------------------------

    let mut f = Function::new(translate_protect_result_name(None), types::boolean());
    f.add_comment("Checking the translate function result".to_string());

    f.add_arg(String::from("st!0"), types::model());
    f.add_arg(String::from("st!1"), types::model());
    f.add_arg(String::from("va"), types::vaddr());
    f.add_arg(String::from("sz"), types::size());
    f.add_arg(String::from("flgs"), types::flags());

    let varstr = "i!0".to_string();
    let forallvars = vec![SortedVar::new(varstr.clone(), types::size())];

    // forall i | 0 <= i < size :: translate (st!0, va + i) == translate (st!1, va + i)
    // forall i :: 0 <= i < size ==> translate (st!0, va + i) == translate (st!1, va + i)
    let constr = Term::land(
        Term::bvge(Term::num(0), Term::ident(varstr.clone())),
        Term::bvlt(Term::ident(varstr.clone()), Term::ident("sz".to_string())),
    );

    let check = Term::bveq(
        Term::fn_apply(
            "translate".to_string(),
            vec![
                Term::ident(String::from("st!0")),
                Term::bvadd(Term::ident("va".to_string()), Term::ident(varstr.clone())),
            ],
        ),
        Term::fn_apply(
            "translate".to_string(),
            vec![
                Term::ident(String::from("st!1")),
                Term::bvadd(Term::ident("va".to_string()), Term::ident(varstr)),
            ],
        ),
    );

    let body = Term::forall(forallvars, constr.implies(check));
    f.add_body(body);

    smt.function(f);
}

pub fn add_matchflags_result_checks(smt: &mut Smt2Context, nparts: usize) {
    // ---------------------------------------------------------------------------------------------
    // Result when mapping
    // ---------------------------------------------------------------------------------------------

    let map = |smt: &mut Smt2Context, idx| {
        let mut f = Function::new(matchflags_map_result_name(idx), types::boolean());
        f.add_comment("Checking the matchflags function result".to_string());

        f.add_arg(String::from("st!0"), types::model());
        f.add_arg(String::from("va"), types::vaddr());
        f.add_arg(String::from("sz"), types::size());
        f.add_arg(String::from("flgs"), types::flags());
        f.add_arg(String::from("pa"), types::paddr());

        let name = if let Some(i) = idx {
            method_part_i_name("matchflags", i)
        } else {
            "matchflags".to_string()
        };

        let body = Term::fn_apply(name, vec![Term::from("st!0"), Term::from("flgs")]);
        f.add_body(body);
        smt.function(f);
    };

    for i in 0..nparts {
        map(smt, Some(i));
    }
    map(smt, None);

    // ---------------------------------------------------------------------------------------------
    // Result when unmapping
    // ---------------------------------------------------------------------------------------------

    let unmap = |smt: &mut Smt2Context, idx| {
        let mut f = Function::new(matchflags_unmap_result_name(idx), types::boolean());
        f.add_comment("Checking the matchflags function result".to_string());

        f.add_arg(String::from("st!0"), types::model());
        f.add_arg(String::from("va"), types::vaddr());
        f.add_arg(String::from("sz"), types::size());
        f.add_arg(String::from("flgs"), types::flags());

        let name = if let Some(i) = idx {
            method_part_i_name("matchflags", i)
        } else {
            "matchflags".to_string()
        };

        let body = Term::fn_apply(name, vec![Term::from("st!0"), Term::from("flgs")]);
        f.add_body(body);
        smt.function(f);
    };

    for i in 0..nparts {
        unmap(smt, Some(i));
    }
    unmap(smt, None);

    // ---------------------------------------------------------------------------------------------
    // Result when protecting
    // ---------------------------------------------------------------------------------------------

    let protect = |smt: &mut Smt2Context, idx| {
        let mut f = Function::new(matchflags_protect_result_name(idx), types::boolean());
        f.add_comment("Checking the matchflags function result".to_string());

        f.add_arg(String::from("st!0"), types::model());
        f.add_arg(String::from("va"), types::vaddr());
        f.add_arg(String::from("sz"), types::size());
        f.add_arg(String::from("flgs"), types::flags());
        // f.add_arg(String::from("pa"), types::paddr());

        let name = if let Some(i) = idx {
            method_part_i_name("matchflags", i)
        } else {
            "matchflags".to_string()
        };

        let body = Term::fn_apply(name, vec![Term::from("st!0"), Term::from("flgs")]);
        f.add_body(body);
        smt.function(f);
    };

    for i in 0..nparts {
        protect(smt, Some(i));
    }
    protect(smt, None);
}

pub fn call_method_assms(m: &VelosiAstMethod, st: &str) -> Term {
    let mut assm_args = vec![Term::from(st)];
    for a in m.params.iter() {
        assm_args.push(Term::ident(a.ident_to_string()));
    }
    let name = method_assms_name(m.ident());
    Term::fn_apply(name, assm_args)
}

pub fn call_method(m: &VelosiAstMethod, args: Vec<Term>) -> Term {
    let mut fn_args = args;
    for v in m.params.iter() {
        fn_args.push(Term::ident(v.ident_to_string()));
    }
    Term::fn_apply(m.ident_to_string(), fn_args)
}

// pub fn call_method_part(m: &VelosiAstMethod, idx: Option<usize>, args: Vec<Term>) -> Term {
//     let mut fn_args = args;
//     for v in m.params.iter() {
//         fn_args.push(Term::ident(v.ident_to_string()));
//     }

//     let name = if let Some(i) = idx {
//         format!("{}.{}", m.ident(), i)
//     } else {
//         m.ident_to_string()
//     };

//     Term::fn_apply(name, fn_args)
// }

pub fn call_method_pre(m: &VelosiAstMethod, idx: Option<usize>, args: Vec<Term>) -> Term {
    let mut check_args = args;
    for a in m.params.iter() {
        check_args.push(Term::ident(a.ident_to_string()));
    }

    let name = if let Some(i) = idx {
        method_precond_i_name(m.ident(), i)
    } else {
        method_precond_name(m.ident())
    };
    Term::fn_apply(name, check_args)
}

pub fn call_method_sempre(m: &VelosiAstMethod, idx: Option<usize>, args: Vec<Term>) -> Term {
    let mut check_args = args;
    for a in m.params.iter() {
        check_args.push(Term::ident(a.ident_to_string()));
    }

    Term::fn_apply(translate_range_name(idx), check_args)
}

pub fn call_method_result_check_part(
    m: &VelosiAstMethod,
    g: &VelosiAstMethod,
    idx: Option<usize>,
    args: Vec<Term>,
) -> Term {
    let name = match (m.ident().as_str(), g.ident().as_str()) {
        ("map", "valid") => valid_map_result_name(idx),
        ("unmap", "valid") => valid_unmap_result_name(idx),
        ("protect", "valid") => valid_protect_result_name(idx),
        ("map", "translate") => translate_map_result_name(idx),
        ("protect", "translate") => translate_protect_result_name(idx),
        ("map", "matchflags") => matchflags_map_result_name(idx),
        ("unmap", "matchflags") => matchflags_unmap_result_name(idx),
        ("protect", "matchflags") => matchflags_protect_result_name(idx),
        (a, b) => unreachable!("case: {} {}", a, b),
    };

    let mut check_args = args;
    for a in m.params.iter() {
        check_args.push(Term::ident(a.ident_to_string()));
    }

    // matchflags need access to the flags but are not provided in unmap
    if (m.ident().as_str(), g.ident().as_str()) == ("unmap", "matchflags") {
        check_args.push(Term::ident("flgs".to_string()));
    }

    Term::fn_apply(name, check_args)
}

pub fn combine_method_params(
    pvars: Vec<SortedVar>,
    p1: &[Rc<VelosiAstParam>],
    p2: &[Rc<VelosiAstParam>],
) -> Vec<SortedVar> {
    // all possible variables
    let mut vars = HashMap::new();
    for v in pvars {
        vars.insert(v.ident.clone(), v);
    }

    for p in p1.iter() {
        if vars.contains_key(p.ident().as_str()) {
            continue;
        }
        let v = SortedVar::new(p.ident_to_string(), types::type_to_smt2(&p.ptype));
        vars.insert(p.ident_to_string(), v);
    }

    for p in p2.iter() {
        if vars.contains_key(p.ident().as_str()) {
            continue;
        }
        let v = SortedVar::new(p.ident_to_string(), types::type_to_smt2(&p.ptype));
        vars.insert(p.ident_to_string(), v);
    }

    let mut res = vec![];
    for (_, v) in vars.into_iter() {
        res.push(v);
    }
    res
}
