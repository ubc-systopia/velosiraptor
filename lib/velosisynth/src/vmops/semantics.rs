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

use smt2::{Smt2Context, SortedVar, Term};
use velosiast::ast::{VelosiAstMethod, VelosiAstUnitSegment};

use crate::{
    model::method::{
        call_method, call_method_assms, call_method_result_check_part, combine_method_params,
    },
    model::types,
    z3::{Z3Query, Z3Ticket, Z3WorkerPool},
    Program,
};

use super::queryhelper::{
    MaybeResult, MultiDimProgramQueries, ProgramBuilder, ProgramQueries, QueryBuilder,
};
use crate::ProgramsIter;

use super::utils;

pub struct SemanticQueryBuilder<T>
where
    T: ProgramBuilder,
{
    /// the programs
    programs: T,
    /// the operation method
    m_op: Rc<VelosiAstMethod>,
    /// the goal method
    m_goal: Rc<VelosiAstMethod>,
    /// the entry in the pre-condition
    idx: Option<usize>,
    /// whether the result should not change
    no_change: bool,
}

impl<T> SemanticQueryBuilder<T>
where
    T: ProgramBuilder,
{
    pub fn new(
        programs: T,
        m_op: Rc<VelosiAstMethod>,
        m_goal: Rc<VelosiAstMethod>,
        idx: Option<usize>,
        no_change: bool,
    ) -> Self {
        Self {
            programs,
            m_op,
            m_goal,
            idx,
            no_change,
        }
    }
}

impl<T> QueryBuilder for SemanticQueryBuilder<T>
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
                prog,
                self.no_change,
            )),
            MaybeResult::Pending => MaybeResult::Pending,
            MaybeResult::None => MaybeResult::None,
        }
    }
}

type SemanticFragmentQueries = ProgramQueries<SemanticQueryBuilder<ProgramsIter>>;
type SemanticBlockQueries = MultiDimProgramQueries<SemanticFragmentQueries>;

pub enum SemanticQueries {
    SingleQuery(SemanticQueryBuilder<ProgramsIter>),
    MultiQuery(SemanticQueryBuilder<SemanticBlockQueries>),
}

impl QueryBuilder for SemanticQueries {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Z3Query> {
        match self {
            Self::SingleQuery(q) => q.next(z3),
            Self::MultiQuery(q) => q.next(z3),
        }
    }
}

pub fn semantic_query(
    unit: &VelosiAstUnitSegment,
    m_op: Rc<VelosiAstMethod>,
    m_goal: Rc<VelosiAstMethod>,
    no_change: bool,
    batch_size: usize,
) -> ProgramQueries<SemanticQueries> {
    if let Some(body) = &m_goal.body {
        if body.result_type().is_boolean() {
            let body = body.clone();
            let mut program_queries = Vec::new();
            for (idx, e) in body.split_cnf().iter().enumerate() {
                let programs = utils::make_program_builder(unit, m_op.as_ref(), e).into_iter();
                let b = SemanticQueryBuilder::new(
                    programs,
                    m_op.clone(),
                    m_goal.clone(),
                    Some(idx),
                    no_change,
                );
                let q = ProgramQueries::with_batchsize(b, batch_size);

                program_queries.push(q);
            }
            let programs = MultiDimProgramQueries::new(program_queries);

            let b = SemanticQueryBuilder::new(programs, m_op, m_goal.clone(), None, no_change);
            ProgramQueries::new(SemanticQueries::MultiQuery(b))
        } else {
            // case 1: we just have a single body element, so no need to split up.

            let programs = utils::make_program_builder(unit, m_op.as_ref(), body).into_iter();
            let b = SemanticQueryBuilder::new(programs, m_op, m_goal.clone(), None, no_change);

            ProgramQueries::with_batchsize(SemanticQueries::SingleQuery(b), batch_size)
        }
    } else {
        unreachable!("all methods should have a body here.");
    }
}

fn program_to_query(
    m_op: &VelosiAstMethod,
    m_goal: &VelosiAstMethod,
    idx: Option<usize>,
    prog: Program,
    no_change: bool,
) -> Z3Query {
    // convert the program to a smt2 term
    let (mut smt, symvars) = prog.to_smt2_term(m_op.ident(), m_op.params.as_slice());

    // build up the pre-conditions
    let pre1 = call_method_assms(m_op, "st!0");
    let pre2 = call_method_assms(m_goal, "st!0");
    let pre = Term::land(pre1, pre2);

    // construct the predicate call

    let m_op_call = call_method(m_op, vec![Term::from("st!0")]);

    let args = if no_change {
        vec![Term::from("st!0"), m_op_call]
    } else {
        vec![m_op_call]
    };

    let m_goal_call = call_method_result_check_part(m_op, m_goal, idx, args);

    // obtain the forall params
    let stvar = SortedVar::new("st!0".to_string(), types::model());
    let vars = combine_method_params(
        vec![stvar],
        m_op.params.as_slice(),
        m_goal.params.as_slice(),
    );

    // get the goal as string
    let goal = m_goal_call.to_string_compact();
    // println!("s goal: {}", goal);

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
    query.set_program(prog).set_goal(goal);
    query
}

pub fn submit_program_query(
    z3: &mut Z3WorkerPool,
    m_op: &VelosiAstMethod,
    m_goal: &VelosiAstMethod,
    idx: Option<usize>,
    prog: Program,
    no_change: bool,
) -> Z3Ticket {
    let query = program_to_query(m_op, m_goal, idx, prog, no_change);
    z3.submit_query(query).expect("failed to submit query")
}
