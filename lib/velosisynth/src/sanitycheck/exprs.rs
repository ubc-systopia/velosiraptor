// Velosiraptor Synthesizer
//
//
// MIT License
//
// Copyright (c) 2023 Systopia Lab, Computer Science, University of British Columbia
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

use std::collections::HashMap;
use std::rc::Rc;

use smt2::{Smt2Context, Term, VarDecl};

use velosiast::ast::VelosiAstExpr;

use crate::error::{VelosiSynthErrorBuilder, VelosiSynthErrorUnsatDef, VelosiSynthIssues};
use crate::model::{expr, types};
use crate::z3::{Z3Query, Z3Result, Z3TaskPriority, Z3Ticket, Z3WorkerPool};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Single Expressions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// checks whether a single expressions can be satisfied
///
/// # Arguments
///
/// * `z3` - the Z3 worker pool
/// * `p1` - the first expression
/// * `i1` - the index of the first expression
///
/// # Returns
///
/// The function returns a Z3Ticket of the submitted query
///
fn expr_query(z3: &mut Z3WorkerPool, e: &VelosiAstExpr, i1: usize) -> Z3Ticket {
    // construct a new SMT2 context
    let mut smt = Smt2Context::new();

    // ---------------------------------------------------------------------------------------------
    // Variable Declarations
    // ---------------------------------------------------------------------------------------------
    //
    // We know that the function signatures have a well-defined arguments, so we can
    // leverage this. In particluar the values:
    //   va: vaddr, sz: size, flgs: flags, pa : paddr
    // So fore ach of them we declare a variable and add it to the context.
    // in addition we add the state avariable

    smt.variable(VarDecl::new(String::from("st"), types::model()));
    smt.variable(VarDecl::new("va".to_string(), types::vaddr()));
    smt.variable(VarDecl::new("sz".to_string(), types::size()));
    smt.variable(VarDecl::new("flgs".to_string(), types::flags()));
    smt.variable(VarDecl::new("pa".to_string(), types::paddr()));

    // ---------------------------------------------------------------------------------------------
    // Assert expressions
    // ---------------------------------------------------------------------------------------------
    //
    // We assert the two expressions. There should be an assignment for each of them.

    let name1 = format!("expr-{i1}");
    smt.assert(Term::named(expr::expr_to_smt2(e, "st"), name1));

    // ---------------------------------------------------------------------------------------------
    // Checking Satisfiability
    // ---------------------------------------------------------------------------------------------
    //
    // Invoke the `checkast` function and obtain the unsat core

    smt.check_sat();
    smt.get_unsat_core();

    // ---------------------------------------------------------------------------------------------
    // Create and Submit query
    // ---------------------------------------------------------------------------------------------
    //
    // Here we push the context to the Z3 and then submit the query to the pool

    let mut smtctx = Smt2Context::new();
    smtctx.level(smt);

    let q = Box::new(Z3Query::from(smtctx));
    z3.submit_query(q, Z3TaskPriority::Medium)
        .expect("failed to submit query")
}

/// checks whether a single expressions can be satisfied
///
pub fn check_expr(z3: &mut Z3WorkerPool, e: &VelosiAstExpr) -> VelosiSynthIssues {
    let mut issues = VelosiSynthIssues::new();

    let ticket = expr_query(z3, e, 1);
    let result = z3.wait_for_result(ticket);

    let mut res = result.result().lines();
    if Some("sat") == res.next() {
        log::debug!(target: "[Z3Synth]", "expr {e} is satisfiable");
    } else {
        // TODO: add the error here
        let msg = "unable to satify expression";
        let e = VelosiSynthErrorBuilder::err(msg.to_string())
            .add_location(e.loc().clone())
            .add_hint("this is the expression that can't be satisfied".to_string())
            .build();
        issues.push(e)
    }

    issues
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Expression Pairs
////////////////////////////////////////////////////////////////////////////////////////////////////

/// checks whether two expressions can be satisfied at the same time
///
/// # Arguments
///
/// * `z3` - the Z3 worker pool
/// * `p1` - the first expression
/// * `i1` - the index of the first expression
/// * `p2` - the second expression
/// * `i2` - the index of the second expression
///
/// # Returns
///
/// The function returns a Z3Ticket of the submitted query
///
fn expr_pair_query(
    z3: &mut Z3WorkerPool,
    e1: &VelosiAstExpr,
    i1: usize,
    e2: &VelosiAstExpr,
    i2: usize,
) -> Z3Ticket {
    // construct a new SMT2 context
    let mut smt = Smt2Context::new();

    // ---------------------------------------------------------------------------------------------
    // Variable Declarations
    // ---------------------------------------------------------------------------------------------
    //
    // We know that the function signatures have a well-defined arguments, so we can
    // leverage this. In particluar the values:
    //   va: vaddr, sz: size, flgs: flags, pa : paddr
    // So fore ach of them we declare a variable and add it to the context.
    // in addition we add the state avariable

    smt.variable(VarDecl::new(String::from("st"), types::model()));
    smt.variable(VarDecl::new("va".to_string(), types::vaddr()));
    smt.variable(VarDecl::new("sz".to_string(), types::size()));
    smt.variable(VarDecl::new("flgs".to_string(), types::flags()));
    smt.variable(VarDecl::new("pa".to_string(), types::paddr()));

    // ---------------------------------------------------------------------------------------------
    // Assert expressions
    // ---------------------------------------------------------------------------------------------
    //
    // We assert the two expressions. There should be an assignment for each of them.

    let name1 = format!("expr-{i1}");
    smt.assert(Term::named(expr::expr_to_smt2(e1, "st"), name1));

    let name2 = format!("expr-{i2}");
    smt.assert(Term::named(expr::expr_to_smt2(e2, "st"), name2));

    // ---------------------------------------------------------------------------------------------
    // Checking Satisfiability
    // ---------------------------------------------------------------------------------------------
    //
    // Invoke the `checkast` function and obtain the unsat core

    smt.check_sat();
    smt.get_unsat_core();

    // ---------------------------------------------------------------------------------------------
    // Create and Submit query
    // ---------------------------------------------------------------------------------------------
    //
    // Here we push the context to the Z3 and then submit the query to the pool

    let mut smtctx = Smt2Context::new();
    smtctx.level(smt);

    let q = Box::new(Z3Query::from(smtctx));
    z3.submit_query(q, Z3TaskPriority::Medium)
        .expect("failed to submit query")
}

pub fn check_expr_pair(
    z3: &mut Z3WorkerPool,
    e1: &VelosiAstExpr,
    e2: &VelosiAstExpr,
) -> VelosiSynthIssues {
    let mut issues = VelosiSynthIssues::new();

    let ticket = expr_pair_query(z3, e1, 1, e2, 2);
    let result = z3.wait_for_result(ticket);

    let mut res = result.result().lines();
    if Some("sat") == res.next() {
        log::debug!(target: "[Z3Synth]", "exprs {e1} and {e1} are satisfiable");
    } else {
        // obtain the unsatcore with the conflicts.
        let conflicts = res.next().expect("expected unsatcore on next line");
        let toks = conflicts[1..conflicts.len() - 1]
            .split(' ')
            .collect::<Vec<&str>>();

        if toks.len() == 2 {
            let msg = "unable to satify constraints";
            let err =
                VelosiSynthErrorUnsatDef::new(msg.to_string(), e1.loc().clone(), e2.loc().clone());
        } else {
            // just one! figure out which one
            let i = toks[0][5..].parse::<usize>().unwrap();
            let exp = if i == 1 { e1 } else { e2 };

            let msg = "unable to satify expression";
            let e = VelosiSynthErrorBuilder::err(msg.to_string())
                .add_location(exp.loc().clone())
                .add_hint("this is the expression that can't be satisfied".to_string())
                .build();
            issues.push(e)
        }
    }

    issues
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Checking all expressions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// checks all expressions in one go
fn all_expr_query(z3: &mut Z3WorkerPool, exprs: &[&VelosiAstExpr]) -> Z3Ticket {
    // construct a new SMT2 context
    let mut smt = Smt2Context::new();

    // ---------------------------------------------------------------------------------------------
    // Variable Declarations
    // ---------------------------------------------------------------------------------------------
    //
    // We know that the function signatures have a well-defined arguments, so we can
    // leverage this. In particluar the values:
    //   va: vaddr, sz: size, flgs: flags, pa : paddr
    // So fore ach of them we declare a variable and add it to the context.
    // in addition we add the state avariable

    smt.variable(VarDecl::new(String::from("st"), types::model()));
    smt.variable(VarDecl::new("va".to_string(), types::vaddr()));
    smt.variable(VarDecl::new("sz".to_string(), types::size()));
    smt.variable(VarDecl::new("flgs".to_string(), types::flags()));
    smt.variable(VarDecl::new("pa".to_string(), types::paddr()));

    // ---------------------------------------------------------------------------------------------
    // Assert expressions
    // ---------------------------------------------------------------------------------------------
    //
    // We assert the two expressions. There should be an assignment for each of them.

    for (i, e) in exprs.iter().enumerate() {
        let name1 = format!("expr-{i}");
        smt.assert(Term::named(expr::expr_to_smt2(e, "st"), name1));
    }

    // ---------------------------------------------------------------------------------------------
    // Checking Satisfiability
    // ---------------------------------------------------------------------------------------------
    //
    // Invoke the `checkast` function and obtain the unsat core

    smt.check_sat();
    smt.get_unsat_core();

    // ---------------------------------------------------------------------------------------------
    // Create and Submit query
    // ---------------------------------------------------------------------------------------------
    //
    // Here we push the context to the Z3 and then submit the query to the pool

    let mut smtctx = Smt2Context::new();
    smtctx.level(smt);

    let q = Box::new(Z3Query::from(smtctx));
    z3.submit_query(q, Z3TaskPriority::Medium)
        .expect("failed to submit query")
}

fn all_expr_check_result(
    z3: &mut Z3WorkerPool,
    exprs: &[&VelosiAstExpr],
    result: &Z3Result,
) -> VelosiSynthIssues {
    let mut issues = VelosiSynthIssues::new();

    // obtain the output lines, if we get `sat` we're done
    let mut res = result.result().lines();
    if Some("sat") == res.next() {
        log::debug!(target: "[Z3Synth]", "all exprs is satisfiable");
        return issues;
    }

    log::debug!(target: "[Z3Synth]", "all exprs is unsatisfiable");

    if result.has_errors() {
        for l in result.collect_errors() {
            let msg = format!("Z3 Error: {l}");
            let e = VelosiSynthErrorBuilder::err(msg).build();
            issues.push(e)
        }
        return issues;
    }

    // obtain the unsatcore with the conflicts.
    let conflicts = res.next().expect("expected unsatcore on next line");
    let toks = conflicts[1..conflicts.len() - 1]
        .split(' ')
        .map(|t| {
            if t.starts_with("expr") {
                let i = t[5..].parse::<usize>().unwrap();
                exprs[i]
            } else {
                println!("{}", result.result());
                panic!("unknown conflict: {}", t);
            }
        })
        .collect::<Vec<&VelosiAstExpr>>();

    if toks.len() == 2 {
        let msg = "unable to satify constraints";
        let err = VelosiSynthErrorUnsatDef::new(
            msg.to_string(),
            toks.first().unwrap().loc().clone(),
            toks.last().unwrap().loc().clone(),
        );
        issues.push(err.into());
    } else {
        panic!("should not happen?");
    }

    issues
}

/// checks all expressions in one go
pub fn check_all_expr(z3: &mut Z3WorkerPool, exprs: &[&VelosiAstExpr]) -> VelosiSynthIssues {
    let ticket = all_expr_query(z3, exprs);
    let result = z3.wait_for_result(ticket);
    all_expr_check_result(z3, exprs, &result)
}

/// checks all expressions pairwise individually
pub fn check_all_expr_pairwise(
    z3: &mut Z3WorkerPool,
    exprs: &[&VelosiAstExpr],
) -> VelosiSynthIssues {
    let mut issues = VelosiSynthIssues::new();

    let mut tickets = HashMap::new();
    for i in 0..exprs.len() {
        for j in i + 1..exprs.len() {
            if exprs[i] != exprs[j] {
                let ticket = expr_pair_query(z3, exprs[i], i, exprs[j], j);
                tickets.insert((i, j), ticket);
            }
        }
    }
    // collect and process the results
    let mut results = Vec::with_capacity(tickets.len());
    while !tickets.is_empty() {
        tickets.retain(|(i, j), ticket| {
            if let Some(res) = z3.get_result(*ticket) {
                results.push((*i, *j, res));
                false
            } else {
                true
            }
        });

        for (i, j, result) in results.drain(..) {
            let mut res = result.result().lines();
            if Some("sat") == res.next() {
                log::debug!(target: "[Z3Synth]", "exprs {} and {} are satisfiable", exprs[i], exprs[j]);
            } else {
                // obtain the unsatcore with the conflicts.
                let conflicts = res.next().expect("expected unsatcore on next line");
                let toks = conflicts[1..conflicts.len() - 1]
                    .split(' ')
                    .collect::<Vec<&str>>();

                if toks.len() == 2 {
                    let msg = "unable to satify constraints";
                    let err = VelosiSynthErrorUnsatDef::new(
                        msg.to_string(),
                        exprs[i].loc().clone(),
                        exprs[j].loc().clone(),
                    );
                    issues.push(err.into())
                } else {
                    // just one! figure out which one
                    let i = toks[0][5..].parse::<usize>().unwrap();
                    let msg = "unable to satify expression";
                    let err = VelosiSynthErrorBuilder::err(msg.to_string())
                        .add_location(exprs[i].loc().clone())
                        .add_hint("this is the expression that can't be satisfied".to_string())
                        .build();
                    issues.push(err)
                }
            }
        }
    }
    issues
}
