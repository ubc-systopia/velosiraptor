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

use std::collections::HashSet;
use std::rc::Rc;

use smt2::{Smt2Context, SortedVar, Term};
use velosiast::ast::{VelosiAstMethod, VelosiAstUnitSegment};

use crate::{
    model::method::{call_method, call_method_assms, call_method_sempre, combine_method_params},
    model::types,
    z3::{Z3Query, Z3TaskPriority, Z3Ticket, Z3WorkerPool},
    Program,
};

use super::{
    queryhelper::{
        MaybeResult, MultiDimProgramQueries, ProgramBuilder, ProgramQueries, QueryBuilder,
    },
    utils::SynthOptions,
};
use crate::ProgramsIter;

use super::utils;

pub struct SemPrecondQueryBuilder<T>
where
    T: ProgramBuilder,
{
    /// the prefix to use for identifiers
    prefix: String,
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

impl<T> SemPrecondQueryBuilder<T>
where
    T: ProgramBuilder,
{
    pub fn new(
        prefix: String,
        programs: T,
        m_op: Rc<VelosiAstMethod>,
        m_goal: Rc<VelosiAstMethod>,
        idx: Option<usize>,
        negate: bool,
    ) -> Self {
        Self {
            prefix,
            programs,
            m_op,
            m_goal,
            negate,
            idx,
        }
    }
}

impl<T> QueryBuilder for SemPrecondQueryBuilder<T>
where
    T: ProgramBuilder,
{
    /// returns the next query to be submitted, or None if all have been submitted
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Box<Z3Query>> {
        match self.programs.next(z3) {
            MaybeResult::Some(prog) => {
                // println!("program! {prog}\n");
                MaybeResult::Some(program_to_query(
                    &self.prefix,
                    &self.m_op,
                    &self.m_goal,
                    self.idx,
                    prog,
                    self.negate,
                    false,
                    false,
                ))
            }
            MaybeResult::Pending => MaybeResult::Pending,
            MaybeResult::None => MaybeResult::None,
        }
    }
}

pub type SemPrecondFragmentQueries = ProgramQueries<SemPrecondQueryBuilder<ProgramsIter>>;
pub type SemPrecondBlockQueries = MultiDimProgramQueries<SemPrecondFragmentQueries>;
pub type SemPrecondQueries = ProgramQueries<SemPrecondQueryBuilder<SemPrecondBlockQueries>>;

pub fn semprecond_query(
    unit: &VelosiAstUnitSegment,
    m_op: Rc<VelosiAstMethod>,
    m_goal: Rc<VelosiAstMethod>,
    negate: bool,
    batch_size: usize,
) -> Option<SemPrecondQueries> {
    if m_goal.ident().as_str() != "translate" {
        println!("{}", m_goal);
        panic!("called with unknown method: {}", m_goal.ident())
    }

    let mut params = HashSet::new();
    for p in m_goal.params.iter() {
        params.insert(p.ident().as_str());
    }

    let mut program_queries = Vec::with_capacity(m_goal.requires.len());
    for (i, pre) in m_goal.requires.iter().enumerate() {
        // if there are no state references, then this is an assumption and we can skip it
        if !pre.has_state_references() {
            continue;
        }

        // if there were variable refernces, we can skip the query as this is handled elsewhere
        if !pre.has_var_references(&params) {
            continue;
        }

        let mut builder = utils::make_program_builder_no_params(unit, pre);
        builder.add_var(String::from("va"));
        builder.add_var(String::from("sz"));

        let programs = builder.into_iter();
        if !programs.has_programs() {
            continue;
        }
        let b = SemPrecondQueryBuilder::new(
            unit.ident_to_string(),
            programs,
            m_op.clone(),
            m_goal.clone(),
            Some(i),
            negate,
        );
        let q = ProgramQueries::with_batchsize(b, batch_size, Z3TaskPriority::Low);
        program_queries.push(q);
    }

    if program_queries.is_empty() {
        None
    } else {
        let programs = MultiDimProgramQueries::new(program_queries);

        let b = SemPrecondQueryBuilder::new(
            unit.ident_to_string(),
            programs,
            m_op,
            m_goal,
            None,
            negate,
        );
        Some(ProgramQueries::new(b, Z3TaskPriority::Medium))
    }
}

fn program_to_query(
    prefix: &str,
    m_op: &VelosiAstMethod,
    m_goal: &VelosiAstMethod,
    idx: Option<usize>,
    prog: Program,
    negate: bool,
    no_change: bool,
    mem_model: bool,
) -> Box<Z3Query> {
    // convert the program to a smt2 term
    let (mut smt, symvars) =
        prog.to_smt2_term(prefix, m_op.ident(), m_op.params.as_slice(), mem_model);

    // build up the pre-conditions
    let pre1 = call_method_assms(m_op, "st!0");
    let pre2 = call_method_assms(m_goal, "st!0");
    let mut pre = Term::land(pre1, pre2);
    if mem_model {
        pre = utils::add_empty_wbuffer_precond(prefix, pre);
    }

    // construct the predicate call
    let m_op_call = call_method(m_op, vec![Term::from("st!0")]);
    let m_goal_call = call_method_sempre(m_op, idx, vec![m_op_call, Term::from("va!")]);

    // obtain the forall params
    let stvar = SortedVar::new("st!0".to_string(), types::model(prefix));
    let vaddr = SortedVar::new("va!".to_string(), types::vaddr(prefix));
    let vars = combine_method_params(
        prefix,
        vec![stvar, vaddr],
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
            format!("!{}", m_goal.requires[i])
        } else {
            m_goal.requires[i].to_string()
        }
    } else {
        m_goal
            .requires
            .iter()
            .filter_map(|p| {
                if p.has_state_references() {
                    if negate {
                        Some(format!("!{p}"))
                    } else {
                        Some(p.to_string())
                    }
                } else {
                    None
                }
            })
            .collect::<Vec<String>>()
            .join(" && ")
    };

    // println!("goal: {}", goal);

    // create and submit query
    let mut query = if no_change {
        Z3Query::new()
    } else {
        Z3Query::from(smtctx)
    };
    query.set_program(prog).set_goal(goal);
    Box::new(query)
}

pub fn submit_program_query(
    z3: &mut Z3WorkerPool,
    prefix: &str,
    m_op: &VelosiAstMethod,
    m_goal: &VelosiAstMethod,
    idx: Option<usize>,
    prog: Program,
    options: SynthOptions,
) -> Z3Ticket {
    let query = program_to_query(
        prefix,
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
