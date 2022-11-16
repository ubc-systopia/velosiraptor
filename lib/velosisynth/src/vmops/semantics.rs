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

use smt2::{Smt2Context, SortedVar, Term};
use velosiast::ast::{VelosiAstMethod, VelosiAstUnitSegment};

use crate::{
    model::method::{
        call_method, call_method_assms, call_method_result_check_part, combine_method_params,
    },
    model::types,
    z3::{Z3Query, Z3Result, Z3Ticket, Z3WorkerPool},
    Program,
};

use super::utils::construct_programs;
use super::TicketOrResult;
use crate::programs::MultiDimIterator;

// submits queries for the method preconditions
pub fn submit_method_semantic_queries(
    z3: &mut Z3WorkerPool,
    unit: &VelosiAstUnitSegment,
    m_op: &VelosiAstMethod,
    m_goal: &VelosiAstMethod,
) -> Vec<Vec<Z3Ticket>> {
    if let Some(body) = &m_goal.body {
        if body.result_type().is_boolean() {
            let body = body.clone();
            let mut res = Vec::new();
            for (idx, e) in body.split_cnf().iter().enumerate() {
                // build the programs
                let progs = construct_programs(unit, m_op, e);

                // submit the queries
                res.push(
                    progs
                        .into_iter()
                        .map(|p| submit_program_query(z3, m_op, m_goal, Some(idx), p))
                        .collect(),
                )
            }
            res
        } else {
            // build the programs
            let progs = construct_programs(unit, m_op, body);

            // submit the queries
            vec![progs
                .into_iter()
                .map(|p| submit_program_query(z3, m_op, m_goal, None, p))
                .collect()]
        }
    } else {
        Vec::new()
    }
}

// submits queries for the method preconditions
pub fn combine_semantic_results_submit_queries(
    z3: &mut Z3WorkerPool,
    m_op: &VelosiAstMethod,
    m_goal: &VelosiAstMethod,
    mut fragments: Vec<Vec<Z3Result>>,
) -> TicketOrResult {
    if fragments.is_empty() {
        //panic!("was empty");
        return TicketOrResult::Result(Vec::new());
    }

    if fragments.len() == 1 {
        let v = fragments.pop().unwrap();
        return TicketOrResult::Result(v);
    }

    // create the multi-dim iterator
    let mut it = MultiDimIterator::from_slice(fragments.as_slice());

    let mut res = Vec::with_capacity(it.len());
    while let Some(conf) = it.next() {
        let prog = conf
            .iter()
            .enumerate()
            .fold(Program::new(), |prog, (i, e)| {
                let p = fragments[i][*e]
                    .query()
                    .program()
                    .expect("program was not set.");
                prog.merge(p)
            });

        let ticket = submit_program_query(z3, m_op, m_goal, None, prog);
        res.push(ticket)
    }

    TicketOrResult::Ticket(res)
}

pub fn submit_program_query(
    z3: &mut Z3WorkerPool,
    m_op: &VelosiAstMethod,
    m_goal: &VelosiAstMethod,
    idx: Option<usize>,
    prog: Program,
) -> Z3Ticket {
    // convert the program to a smt2 term
    let (mut smt, symvars) = prog.to_smt2_term(m_op.ident_as_str(), m_op.params.as_slice());

    // build up the pre-conditions
    let pre1 = call_method_assms(m_op, "st!0");
    let pre2 = call_method_assms(m_goal, "st!0");
    let pre = Term::land(pre1, pre2);

    // construct the predicate call
    let m_op_call = call_method(m_op, vec![Term::from("st!0")]);
    let m_goal_call = call_method_result_check_part(m_op, m_goal, idx, vec![m_op_call]);

    // obtain the forall params
    let stvar = SortedVar::new("st!0".to_string(), types::model());
    let vars = combine_method_params(
        vec![stvar],
        m_op.params.as_slice(),
        m_goal.params.as_slice(),
    );

    let t = Term::forall(vars, pre.implies(m_goal_call));

    // assert and check sat
    smt.assert(t);
    smt.check_sat();

    // add the printing of the symvars
    symvars.add_get_values(&mut smt);

    // now form a new context with the smt context in a new level
    let mut smtctx = Smt2Context::new();
    smtctx.subsection(String::from("Verification"));
    smtctx.level(smt);

    // create and submit query
    let mut query = Z3Query::from(smtctx);
    query.set_program(prog);

    z3.submit_query(query).expect("failed to submit query")
}
