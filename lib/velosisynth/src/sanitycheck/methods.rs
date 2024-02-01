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

use smt2::{Smt2Context, Term, VarDecl};

use velosiast::ast::{VelosiAstExpr, VelosiAstMethod, VelosiAstUnitSegment};

use crate::error::{VelosiSynthErrorBuilder, VelosiSynthErrorUnsatDef, VelosiSynthIssues};
use crate::model::{expr, types};
use crate::z3::{Z3Query, Z3Result, Z3TaskPriority, Z3Ticket, Z3WorkerPool};

/// checks whether the the preconditions of a function can be satisfied
///
/// This query asserts all preconditions and and method body (if it's a boolean function)
/// and checks whether there is a satisfiable assignment to the variables. Note, this query
/// will return one of the unsatisfiable conditions and not *all* of them.
///
/// # Arguments
///
/// * z3 - the Z3 worker pool
/// * m - the method
fn method_precond_sat_query(z3: &mut Z3WorkerPool, prefix: &str, m: &VelosiAstMethod) -> Z3Ticket {
    // construct a new SMT2 context
    let mut smt = Smt2Context::new();

    smt.comment(format!("SANITYCHECK:  {}()", m.ident_to_string()));

    // ---------------------------------------------------------------------------------------------
    // Variable Declarations
    // ---------------------------------------------------------------------------------------------

    smt.variable(VarDecl::new(String::from("st"), types::model(prefix)));
    for param in m.params.iter() {
        smt.variable(VarDecl::new(
            param.ident_to_string(),
            types::type_to_smt2(prefix, &param.ptype),
        ));
    }

    // ---------------------------------------------------------------------------------------------
    // Adding Asserts for the pre-conditions and the body, if it's boolean
    // ---------------------------------------------------------------------------------------------

    for (i, e) in m.requires.iter().enumerate() {
        smt.comment(format!("pre-{}: {}", i, e));
        smt.assert(Term::named(
            expr::expr_to_smt2(prefix, e, "st"),
            format!("pre-{i}"),
        ));
    }

    if let (Some(body), true) = (&m.body, m.rtype.is_boolean()) {
        smt.comment(format!("body: {}", body));
        for (i, e) in body.split_cnf().iter().enumerate() {
            smt.assert(Term::named(
                expr::expr_to_smt2(prefix, e.as_ref(), "st"),
                format!("body-{i}"),
            ));
        }
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

fn method_precond_sat_results(
    z3: &mut Z3WorkerPool,
    prefix: &str,
    m: &VelosiAstMethod,
    result: &Z3Result,
) -> VelosiSynthIssues {
    let mut issues = VelosiSynthIssues::new();

    // obtain the output lines, if we get `sat` we're done
    let mut res = result.result().lines();
    if Some("sat") == res.next() {
        log::info!(target: "[Z3Synth]", "method {} is satisfiable", m.ident());
        return issues;
    }

    log::info!(target: "[Z3Synth]", "method {} is unsatisfiable", m.ident());

    if result.has_errors() {
        for l in result.collect_errors() {
            let msg = format!("Z3 Error: {l}");
            let e = VelosiSynthErrorBuilder::err(msg).build();
            issues.push(e)
        }
        return issues;
    }

    // there has been issues, so we re-run the individual queries now

    log::info!(target: "[Z3Synth]", "rerunning individual queries for method {}", m.ident());

    let body_exprs = match (&m.body, m.rtype.is_boolean()) {
        (Some(body), true) => body.split_cnf(),
        _ => Vec::new(),
    };

    let mut exprs: Vec<&VelosiAstExpr> = body_exprs.iter().map(|e| e.as_ref()).collect();
    exprs.extend(m.requires.iter().map(|e| e.as_ref()));

    let conflicts = res.next().expect("expected unsatcore on next line");
    let toks = conflicts[1..conflicts.len() - 1]
        .split(' ')
        .map(|s| {
            let i = if s.starts_with("pre-") {
                s[4..].parse::<usize>().unwrap()
            } else {
                s[5..].parse::<usize>().unwrap()
            };
            exprs[i]
        })
        .collect::<Vec<_>>();

    let locs = toks.iter().map(|e| e.loc().clone()).collect::<Vec<_>>();
    let msg = "unable to satify constraints";
    let err = VelosiSynthErrorUnsatDef::new(msg.to_string(), locs);
    issues.push(err.into());

    let issues_new = super::check_all_expr_pairwise(z3, prefix, exprs.as_slice());

    if issues_new.is_ok() {
        issues
    } else {
        issues_new
    }
}

/// checks the methods for
pub fn check_methods(z3: &mut Z3WorkerPool, unit: &VelosiAstUnitSegment) -> VelosiSynthIssues {
    let mut issues = VelosiSynthIssues::new();

    // issue the queries for checking the methods for satisfiability
    let mut tickets = HashMap::new();
    for m in unit.methods() {
        if !m.recommends_sanity_check() {
            log::warn!(target: "[Z3Synth::Sanitycheck]",  "skipping method {} (!recommmends_sanity_check)", m.ident());
            continue;
        }

        // skip methods that would not result in queries
        if m.requires.is_empty() && m.body.is_none() {
            log::warn!(target: "[Z3Synth::Sanitycheck]",  "skipping method {} (requires/body)", m.ident());
            continue;
        }
        tickets.insert(
            m.ident().as_str(),
            (m, method_precond_sat_query(z3, unit.ident(), m)),
        );
    }

    // collect and process the results
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
            issues.merge(method_precond_sat_results(z3, unit.ident(), m, &result))
        }
    }

    issues
}
