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
    z3::{Z3Query, Z3TaskPriority, Z3Ticket, Z3WorkerPool},
    Program,
};

use super::{
    queryhelper::{
        MaybeResult, MultiDimProgramQueries, ProgramBuilder, ProgramQueries, QueryBuilder,
        SequentialProgramQueries,
    },
    utils::SynthOptions,
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
    /// whether or not to negate the body
    negate: bool,
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
        negate: bool,
        no_change: bool,
    ) -> Self {
        Self {
            programs,
            m_op,
            m_goal,
            idx,
            negate,
            no_change,
        }
    }
}

impl<T> QueryBuilder for SemanticQueryBuilder<T>
where
    T: ProgramBuilder,
{
    /// returns the next query to be submitted, or None if all have been submitted
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Box<Z3Query>> {
        match self.programs.next(z3) {
            MaybeResult::Some(prog) => MaybeResult::Some(program_to_query(
                &self.m_op,
                &self.m_goal,
                self.idx,
                prog,
                self.negate,
                self.no_change,
                false,
            )),
            MaybeResult::Pending => MaybeResult::Pending,
            MaybeResult::None => MaybeResult::None,
        }
    }
}

type SemanticFragmentQueries = ProgramQueries<SemanticQueryBuilder<ProgramsIter>>;
type SemanticBlockQueries = MultiDimProgramQueries<SemanticFragmentQueries>;
type SemanticBlockQueriesNegated = SequentialProgramQueries<SemanticFragmentQueries>;

pub enum SemanticQueries {
    SingleQuery(SemanticQueryBuilder<ProgramsIter>),
    MultiQuery(SemanticQueryBuilder<SemanticBlockQueries>),
    MultiQueryNegated(SemanticQueryBuilder<SemanticBlockQueriesNegated>),
}

impl QueryBuilder for SemanticQueries {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Box<Z3Query>> {
        match self {
            Self::SingleQuery(q) => q.next(z3),
            Self::MultiQuery(q) => q.next(z3),
            Self::MultiQueryNegated(q) => q.next(z3),
        }
    }
}

pub fn semantic_query(
    unit: &VelosiAstUnitSegment,
    m_op: Rc<VelosiAstMethod>,
    m_goal: Rc<VelosiAstMethod>,
    m_cond: &VelosiAstMethod,
    negate: bool,
    no_change: bool,
    batch_size: usize,
) -> Option<ProgramQueries<SemanticQueries>> {
    if let Some(body) = &m_goal.body {
        if body.result_type().is_boolean() {
            let body = body.clone();
            let mut program_queries = Vec::new();
            for (idx, e) in body.split_cnf().iter().enumerate() {
                let programs = utils::make_program_builder(unit, m_op.as_ref(), e).into_iter();
                if !programs.has_programs() {
                    continue;
                }
                let b = SemanticQueryBuilder::new(
                    programs,
                    m_op.clone(),
                    m_goal.clone(),
                    Some(idx),
                    negate,
                    no_change,
                );
                let q = ProgramQueries::with_batchsize(b, batch_size, Z3TaskPriority::Low);

                program_queries.push(q);
            }

            if program_queries.is_empty() {
                None
            } else if negate {
                let programs = SequentialProgramQueries::new(program_queries);
                let b = SemanticQueryBuilder::new(
                    programs,
                    m_op,
                    m_goal.clone(),
                    None,
                    negate,
                    no_change,
                );
                Some(ProgramQueries::new(
                    SemanticQueries::MultiQueryNegated(b),
                    Z3TaskPriority::Medium,
                ))
            } else {
                let programs = MultiDimProgramQueries::new(program_queries);
                let b = SemanticQueryBuilder::new(
                    programs,
                    m_op,
                    m_goal.clone(),
                    None,
                    negate,
                    no_change,
                );
                Some(ProgramQueries::new(
                    SemanticQueries::MultiQuery(b),
                    Z3TaskPriority::Medium,
                ))
            }
        } else {
            // case 1: we just have a single body element, so no need to split up.

            // here we have the the case where we need to synthesize for the result of translate

            let mut builder = if no_change {
                let body = m_cond.body.as_ref().unwrap();

                // utils::make_program_builder_no_params(unit, body)
                utils::make_program_builder(unit, m_op.as_ref(), body)
            } else {
                utils::make_program_builder_no_params(unit, body)
                // utils::make_program_builder(unit, m_op.as_ref(), body).into_iter()
            };

            if m_op.get_param("va").is_some() {
                builder.add_var(String::from("va"));
            }

            if m_op.get_param("pa").is_some() {
                builder.add_var(String::from("pa"));
            }

            let programs = builder.into_iter();

            // XXX: this produces programs where it shouldn't...
            if !programs.has_programs() {
                None
            } else {
                let b = SemanticQueryBuilder::new(
                    programs,
                    m_op,
                    m_goal.clone(),
                    None,
                    negate,
                    no_change,
                );

                Some(ProgramQueries::with_batchsize(
                    SemanticQueries::SingleQuery(b),
                    batch_size,
                    Z3TaskPriority::Low,
                ))
            }
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
    negate: bool,
    no_change: bool,
    mem_model: bool,
) -> Box<Z3Query> {
    // convert the program to a smt2 term
    let (mut smt, symvars) = prog.to_smt2_term(m_op.ident(), m_op.params.as_slice(), mem_model);

    // build up the pre-conditions
    let pre1 = call_method_assms(m_op, "st!0");
    let pre2 = call_method_assms(m_goal, "st!0");
    let mut pre = Term::land(pre1, pre2);
    if mem_model {
        pre = utils::add_empty_wbuffer_precond(pre);
    }

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
    let mut goal = m_goal_call.to_string_compact();
    if negate {
        goal = format!("!{}", goal)
    }
    // println!("s goal: {}", goal);

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

    // create and submit query
    let mut query = Z3Query::from(smtctx);
    query.set_program(prog).set_goal(goal);
    Box::new(query)
}

pub fn submit_program_query(
    z3: &mut Z3WorkerPool,
    m_op: &VelosiAstMethod,
    m_goal: &VelosiAstMethod,
    idx: Option<usize>,
    prog: Program,
    options: SynthOptions,
) -> Z3Ticket {
    let query = program_to_query(
        m_op,
        m_goal,
        idx,
        prog,
        options.negate,
        options.no_change,
        options.mem_model,
    );
    z3.submit_query(query, Z3TaskPriority::High)
        .expect("failed to submit query")
}
