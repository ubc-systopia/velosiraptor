// Velosiraptor Synthesizer
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

use std::rc::Rc;
use std::collections::HashMap;

use smt2::{Smt2Context, Term, VarDecl};

use velosiast::ast::{VelosiAstExpr, VelosiAstMethod, VelosiAstUnitSegment};

use crate::error::{VelosiSynthErrorBuilder, VelosiSynthErrorUnsatDef, VelosiSynthIssues};
use crate::model::{expr, types};
use crate::z3::{Z3Query, Z3Result, Z3TaskPriority, Z3Ticket, Z3WorkerPool};

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
fn expr_pair_sat_query(
    z3: &mut Z3WorkerPool,
    p1: &VelosiAstExpr,
    i1: usize,
    p2: &VelosiAstExpr,
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

    let name1 = format!("fn_1-{i1}");
    smt.assert(Term::named(expr::expr_to_smt2(p1, "st"), name1));

    let name2 = format!("fn_2-{i2}");
    smt.assert(Term::named(expr::expr_to_smt2(p2, "st"), name2));

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
fn expr_sat_query(z3: &mut Z3WorkerPool, p1: &VelosiAstExpr, i1: usize) -> Z3Ticket {
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

    let name1 = format!("fn_1-{i1}");
    smt.assert(Term::named(expr::expr_to_smt2(p1, "st"), name1));

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


/// checks whether the the preconditions of a function can be satisfied
fn method_precond_sat_query(z3: &mut Z3WorkerPool, m: &VelosiAstMethod) -> Z3Ticket
{
    // construct a new SMT2 context
    let mut smt = Smt2Context::new();

    // ---------------------------------------------------------------------------------------------
    // Variable Declarations
    // ---------------------------------------------------------------------------------------------

    smt.variable(VarDecl::new(String::from("st"), types::model()));
    for param in m.params.iter() {
        smt.variable(VarDecl::new(param.ident_to_string(),types::type_to_smt2(&param.ptype)));
    }

    // ---------------------------------------------------------------------------------------------
    // Adding Asserts for the pre-conditions and the body, if it's boolean
    // ---------------------------------------------------------------------------------------------

    for (i, e) in m.requires.iter().enumerate() {
        smt.assert(Term::named(expr::expr_to_smt2(e, "st"), format!("pre-{i}")));
    }

    match (&m.body, m.rtype.is_boolean()) {
        (Some(e), true) => {
            smt.assert(Term::named(expr::expr_to_smt2(e.as_ref(), "st"), format!("body")));
        }
        _ => ()
    }

    // ---------------------------------------------------------------------------------------------
    // Checking Satisfiability
    // ---------------------------------------------------------------------------------------------

    smt.check_sat();
    smt.get_unsat_core();

    // ---------------------------------------------------------------------------------------------
    // Create the query context and submit it
    // ---------------------------------------------------------------------------------------------

    let mut smtctx = Smt2Context::new();
    smtctx.level(smt);

    let q = Box::new(Z3Query::from(smtctx));
    z3.submit_query(q, Z3TaskPriority::Medium)
        .expect("failed to submit query")
}

fn method_precond_sat_results(z3: &mut Z3WorkerPool, m: &VelosiAstMethod, result: &Z3Result) -> VelosiSynthIssues
{
    let mut issues = VelosiSynthIssues::new();

    issues
}

/// checks the methods for
pub fn check_methods(z3: &mut Z3WorkerPool, unit: &VelosiAstUnitSegment) -> VelosiSynthIssues {
    let mut issues = VelosiSynthIssues::new();
    let mut tickets = HashMap::new();
    for m in unit.methods() {
        // skip methods that would not result in queries
        if m.requires.is_empty() && m.body.is_none() && m.rtype.is_boolean() {
            continue;
        }

        tickets.insert(m.ident().as_str(), (m, method_precond_sat_query(z3, m)));
    }

    let mut results = Vec::with_capacity(tickets.len());
    while !tickets.is_empty() {
        tickets.retain(|_k, (m, ticket)| {
            if let Some(res) = z3.get_result(*ticket) {
                results.push((*m, res));
                false
            } else {
                true
            }
        });

        for (m, result) in results.drain(..) {
            issues.merge(method_precond_sat_results(z3, m, &result));
        }
    }

    for (m, result) in results.drain(..) {
        issues.merge(method_precond_sat_results(z3, m, &result));
    }

    issues
}


fn check_satisfy_fn_pair(
    z3: &mut Z3WorkerPool,
    fn_1: &VelosiAstMethod,
    fn_2: &VelosiAstMethod,
) -> Vec<Z3Ticket> {
    let mut tickets = Vec::new();

    let same = fn_1 == fn_2;

    // TODO: here we have the opportunity to skip checks that are already run.
    //       by checking the expressions

    for (i1, p1) in fn_1.requires.iter().enumerate() {
        for (i2, p2) in fn_2.requires.iter().enumerate() {
            // if we have the same function, then we can skip
            if same && i2 < i1 {
                continue;
            }
            let ticket = expr_pair_sat_query(z3, p1, i1, p2, i2);
            tickets.push(ticket);
        }
    }
    tickets
}

fn check_satisfy_fn(z3: &mut Z3WorkerPool, fn_1: &VelosiAstMethod) -> Vec<Z3Ticket> {
    let mut tickets = Vec::new();

    // TODO: here we have the opportunity to skip checks that are already run.
    //       by checking the expressions

    for (i1, p1) in fn_1.requires.iter().enumerate() {
        for (i2, p2) in fn_1.requires.iter().enumerate().skip(i1) {
            let ticket = expr_pair_sat_query(z3, p1, i1, p2, i2);
            tickets.push(ticket);
        }
    }

    tickets
}

fn check_satisfy_fn_results(
    z3: &mut Z3WorkerPool,
    tickets: Vec<Z3Ticket>,
    fn_1: &VelosiAstMethod,
    fn_2: &VelosiAstMethod,
) -> VelosiSynthIssues {
    let mut issues = VelosiSynthIssues::new();

    for ticket in tickets.into_iter() {
        let result = z3.wait_for_result(ticket);

        // obtain the output lines, if we get `sat` we're done
        let mut res = result.result().lines();
        if Some("sat") == res.next() {
            continue;
        }

        if result.has_errors() {
            for l in result.collect_errors() {
                let msg = format!("Z3 Error: {l}");
                let e = VelosiSynthErrorBuilder::err(msg).build();
                issues.push(e)
            }
            continue;
        }

        // obtain the unsatcore with the conflicts.
        let conflicts = res.next().unwrap();
        let mut toks = conflicts[1..conflicts.len() - 1]
            .split(' ')
            .collect::<Vec<&str>>();

        let toks = toks
            .iter_mut()
            .map(|t| {
                if t.starts_with("fn_1") {
                    let i = t[5..].parse::<usize>().unwrap();
                    &fn_1.requires[i]
                } else if t.starts_with("fn_2") {
                    let i = t[5..].parse::<usize>().unwrap();
                    &fn_2.requires[i]
                } else {
                    println!("{}", result.result());
                    panic!("unknown conflict: {}", t);
                }
            })
            .collect::<Vec<&Rc<VelosiAstExpr>>>();

        if toks.len() == 2 {
            let msg = "unable to satify constraints";
            let err = VelosiSynthErrorUnsatDef::new(
                msg.to_string(),
                toks.first().unwrap().loc().clone(),
                toks.last().unwrap().loc().clone(),
            );
            issues.push(err.into());
        } else {
        }
    }
    issues
}

/// Checks the satisfiability of the pre-conditions of the given functions
pub fn check_precondition_satisfiability(
    z3: &mut Z3WorkerPool,
    unit: &VelosiAstUnitSegment,
    fname: &str,
) -> Result<(), VelosiSynthIssues> {
    let mut issues = VelosiSynthIssues::new();

    // must be one of htese
    assert!(matches!(fname, "map" | "unmap" | "protect"));

    // get the translate function
    let t_fn = unit.get_method("translate").unwrap();
    // get the matchflags function
    let f_fn = unit.get_method("matchflags").unwrap();

    // get the unit under test
    let m_fn = unit.get_method(fname).unwrap();

    let tickets1 = check_satisfy_fn_pair(z3, t_fn, f_fn);
    let tickets2 = check_satisfy_fn_pair(z3, t_fn, m_fn);
    let tickets3 = check_satisfy_fn_pair(z3, f_fn, m_fn);

    let tickets4 = check_satisfy_fn(z3, f_fn);
    let tickets5 = check_satisfy_fn(z3, m_fn);
    let tickets6 = check_satisfy_fn(z3, t_fn);

    issues.merge(check_satisfy_fn_results(z3, tickets1, t_fn, f_fn));
    issues.merge(check_satisfy_fn_results(z3, tickets2, t_fn, m_fn));
    issues.merge(check_satisfy_fn_results(z3, tickets3, t_fn, f_fn));

    issues.merge(check_satisfy_fn_results(z3, tickets4, f_fn, f_fn));
    issues.merge(check_satisfy_fn_results(z3, tickets5, m_fn, m_fn));
    issues.merge(check_satisfy_fn_results(z3, tickets6, t_fn, t_fn));

    if issues.is_ok() {
        Ok(())
    } else {
        Err(issues)
    }
}
