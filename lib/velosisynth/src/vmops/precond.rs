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

//! Synthesis of Virtual Memory Operations: Map

use std::rc::Rc;

use smt2::{Smt2Context, SortedVar, Term};
use velosiast::ast::{VelosiAstMethod, VelosiAstUnitSegment};

use crate::{
    model::method::{call_method, call_method_assms, call_method_pre, combine_method_params},
    model::types,
    z3::{Z3Query, Z3Result, Z3Ticket, Z3WorkerPool},
    Program,
};

use super::queryhelper::{
    MaybeResult, MultiDimProgramQueries, ProgramBuilder, ProgramQueries, QueryBuilder,
};
use crate::programs::MultiDimIterator;
use crate::ProgramsIter;

use super::utils;

pub struct PrecondQueryBuilder<T>
where
    T: ProgramBuilder,
{
    /// the programs
    programs: T,
    /// the operation method
    m_op: Rc<VelosiAstMethod>,
    /// the goal method
    m_goal: Rc<VelosiAstMethod>,
    /// whether or not to negate the preconditino
    negate: bool,
    /// the entry in the pre-condition
    idx: Option<usize>,
}

impl<T> PrecondQueryBuilder<T>
where
    T: ProgramBuilder,
{
    pub fn new(
        programs: T,
        m_op: Rc<VelosiAstMethod>,
        m_goal: Rc<VelosiAstMethod>,
        idx: Option<usize>,
        negate: bool,
    ) -> Self {
        Self {
            programs,
            m_op,
            m_goal,
            negate,
            idx,
        }
    }
}

impl<T> QueryBuilder for PrecondQueryBuilder<T>
where
    T: ProgramBuilder,
{
    /// returns the next query to be submitted, or None if all have been submitted
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Z3Query> {
        match self.programs.next(z3) {
            MaybeResult::Some(prog) => MaybeResult::Some(program_to_query(
                &self.m_op,
                &self.m_goal,
                self.idx,
                self.negate,
                prog,
            )),
            MaybeResult::Pending => MaybeResult::Pending,
            MaybeResult::None => MaybeResult::None,
        }
    }
}

pub type PrecondFragmentQueries = ProgramQueries<PrecondQueryBuilder<ProgramsIter>>;
pub type PrecondBlockQueries = MultiDimProgramQueries<PrecondFragmentQueries>;
pub type PrecondQueries = ProgramQueries<PrecondQueryBuilder<PrecondBlockQueries>>;

const CONFIG_BATCH_SIZE: usize = 5;

pub fn precond_query(
    unit: &VelosiAstUnitSegment,
    m_op: Rc<VelosiAstMethod>,
    m_goal: Rc<VelosiAstMethod>,
    negate: bool,
) -> PrecondQueries {
    let mut program_queries = Vec::with_capacity(m_goal.requires.len());
    for (i, pre) in m_goal.requires.iter().enumerate() {
        if !pre.has_state_references() {
            continue;
        }
        let programs = utils::make_program_builder(unit, m_goal.as_ref(), pre).into_iter();
        let b = PrecondQueryBuilder::new(programs, m_op.clone(), m_goal.clone(), Some(i), negate);
        let q = ProgramQueries::with_batchsize(b, CONFIG_BATCH_SIZE);
        program_queries.push(q);
    }

    let programs = MultiDimProgramQueries::new(program_queries);

    let b = PrecondQueryBuilder::new(programs, m_op, m_goal, None, negate);
    ProgramQueries::new(b)
}

// submits queries for the method preconditions
pub fn submit_method_precond_queries(
    z3: &mut Z3WorkerPool,
    unit: &VelosiAstUnitSegment,
    m_op: &VelosiAstMethod,
    m_goal: &VelosiAstMethod,
    negate: bool,
) -> Vec<Vec<Z3Ticket>> {
    let mut all_tickets = Vec::with_capacity(m_goal.requires.len());

    // if we have no state references in the pre-condition, then we don't nee do establish
    // this and we can skip this part of the pre-condition
    for (i, pre) in m_goal
        .requires
        .iter()
        .filter(|p| p.has_state_references())
        .enumerate()
    {
        // build the programs
        let progs = utils::construct_programs(unit, m_goal, pre);

        // submit the queries
        let tickets = progs
            .into_iter()
            .map(|p| submit_program_query(z3, m_op, m_goal, Some(i), negate, p))
            .collect();
        all_tickets.push(tickets);
    }

    all_tickets
}

fn program_to_query(
    m_op: &VelosiAstMethod,
    m_goal: &VelosiAstMethod,
    idx: Option<usize>,
    negate: bool,
    prog: Program,
) -> Z3Query {
    // convert the program to a smt2 term
    let (mut smt, symvars) = prog.to_smt2_term(m_op.ident_as_str(), m_op.params.as_slice());

    // build up the pre-conditions
    let pre1 = call_method_assms(m_op, "st!0");
    let pre2 = call_method_assms(m_goal, "st!0");
    let pre = Term::land(pre1, pre2);

    // construct the predicate call
    let m_op_call = call_method(m_op, vec![Term::from("st!0")]);
    let m_goal_call = call_method_pre(m_goal, idx, vec![m_op_call]);

    // obtain the forall params
    let stvar = SortedVar::new("st!0".to_string(), types::model());
    let vars = combine_method_params(
        vec![stvar],
        m_op.params.as_slice(),
        m_goal.params.as_slice(),
    );

    // build up the term
    let t = if negate {
        Term::forall(vars, pre.implies(Term::lnot(m_goal_call)))
    } else {
        Term::forall(vars, pre.implies(m_goal_call))
    };

    // assert and check sat
    smt.assert(t);
    smt.check_sat();

    // add the printing of the symvars
    symvars.add_get_values(&mut smt);

    // now form a new context with the smt context in a new level
    let mut smtctx = Smt2Context::new();
    smtctx.subsection(String::from("Verification"));
    smtctx.level(smt);

    // get the goal as string
    let goal = if let Some(i) = idx {
        if negate {
            format!("!{}", m_goal.requires[i].to_string())
        } else {
            m_goal.requires[i].to_string()
        }
    } else {
        m_goal
            .requires
            .iter()
            .map(|p| {
                if negate {
                    format!("!{}", p.to_string())
                } else {
                    p.to_string()
                }
            })
            .collect::<Vec<String>>()
            .join(" && ")
    };

    // create and submit query
    let mut query = Z3Query::from(smtctx);
    query.set_program(prog).set_goal(goal);
    query
}

pub fn submit_program_query(
    z3: &mut Z3WorkerPool,
    m_op: &VelosiAstMethod,
    m_goal: &VelosiAstMethod,
    idx: Option<usize>,
    negate: bool,
    prog: Program,
) -> Z3Ticket {
    let query = program_to_query(m_op, m_goal, idx, negate, prog);
    z3.submit_query(query).expect("failed to submit query")
}
