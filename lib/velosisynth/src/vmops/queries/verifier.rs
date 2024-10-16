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

//! Query Verifier

use std::collections::LinkedList;
/// std imports
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// library imports
use smt2::{Smt2Context, SortedVar, Term, VarBinding};
use velosiast::ast::{VelosiAstExpr, VelosiAstMethod};

// carte imports
use crate::{
    model::expr::expr_to_smt2,
    model::method::{call_method, call_method_assms},
    model::types,
    z3::{Z3Query, Z3TaskPriority, Z3Ticket, Z3WorkerPool},
    Program,
};

//use super::queryhelper::{MaybeResult, ProgramBuilder, QueryBuilder};
use super::MaybeResult;

// use crate::ProgramsIter;

use super::utils;
use super::ProgramBuilder;

use crate::DEFAULT_BATCH_SIZE;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Program Verifier
////////////////////////////////////////////////////////////////////////////////////////////////////

/// The Program Verifier
///
/// The program verifier takes the programs that are generated by the program builder and submits
/// the queries to Z3 for verification. It does submit a batch of queries at a time.
pub struct ProgramVerifier {
    /// prefix of the methods etc
    prefix: Rc<String>,
    /// sequence of queries to be submitted
    programs: Box<dyn ProgramBuilder>,
    /// the priority of the task
    priority: Z3TaskPriority,
    /// the submitted/in-flight queries
    submitted: LinkedList<Z3Ticket>,
    /// programs that had SAT results
    completed: LinkedList<Program>,
    /// the batch size for submiting queries
    batch_size: usize,
    /// whether we're done processing
    queries_done: bool,
    /// statistics on the number of queries run
    stat_num_queries: usize,
    /// statistics on the number of queries that turned out to be SAT
    stat_num_sat: usize,
}

impl ProgramVerifier {
    /// creates a new query verifier for the queries with the given priority
    pub fn new(
        prefix: Rc<String>,
        queries: Box<dyn ProgramBuilder>,
        priority: Z3TaskPriority,
    ) -> Self {
        Self::with_batchsize(prefix, queries, DEFAULT_BATCH_SIZE, priority)
    }

    /// creates a new query verifier for the queries with the given priority and batch size
    pub fn with_batchsize(
        prefix: Rc<String>,
        programs: Box<dyn ProgramBuilder>,
        batch_size: usize,
        priority: Z3TaskPriority,
    ) -> Self {
        let batch_size = std::cmp::max(batch_size, 1);
        ProgramVerifier {
            prefix,
            programs,
            priority,
            submitted: LinkedList::new(),
            completed: LinkedList::new(),
            batch_size,
            queries_done: false,
            stat_num_queries: 0,
            stat_num_sat: 0,
        }
    }

    fn to_smt_query(&self, prog: Program) -> Box<Z3Query> {
        let m_op = self.programs.m_op();
        let assms = self.programs.assms();
        let goal_expr = self.programs.goal_expr();

        // log::warn!("TODO: handle the mem_model correctly!");
        let mem_model = false;

        // -----------------------------------------------------------------------------------------
        // Setup the pre-conditions
        // -----------------------------------------------------------------------------------------

        // obtain the assumptions of the operation method (map/protect/unmap)
        let pre1 = call_method_assms(m_op, "st!0");

        // add the assumptions of the program
        // TODO: have this as a separate function?
        let mut pre = assms
            .iter()
            .fold(pre1, |acc, assm| Term::land(acc, assm.clone()));

        if mem_model {
            pre = utils::add_empty_wbuffer_precond(self.prefix.as_str(), pre);
        }

        // convert the program to a smt2 term
        let (mut smt, symvars) = prog.to_smt2_term(
            self.prefix.as_str(),
            m_op.ident(),
            m_op.params.as_slice(),
            mem_model,
        );

        // -----------------------------------------------------------------------------------------
        // Variable setup
        // -----------------------------------------------------------------------------------------

        // obtain the forall params, let's just add all of them
        let vars = vec![
            SortedVar::new("st!0".to_string(), types::model(self.prefix.as_str())),
            SortedVar::new("va".to_string(), types::vaddr(self.prefix.as_str())),
            SortedVar::new("pa".to_string(), types::paddr(self.prefix.as_str())),
            SortedVar::new("sz".to_string(), types::size(self.prefix.as_str())),
            SortedVar::new("flgs".to_string(), types::flags(self.prefix.as_str())),
        ];

        // apply the program (i.e., call the corresponding function)
        let m_op_call = call_method(m_op, vec![Term::from("st!0")]);

        // form the implication `let st = OP() in pre => goal`
        let impl_term = Term::Let(
            vec![VarBinding::new("st".to_string(), m_op_call)],
            Box::new(pre.implies(expr_to_smt2(self.prefix.as_str(), &goal_expr, "st"))),
        );

        // build the forall term for the query
        let t_assert = Term::forall(vars, impl_term);

        // get the goal string for the query
        let goal_str = t_assert.to_string();

        // assert the query term
        smt.assert(t_assert);
        smt.check_sat();

        // add the printing of the symvars
        symvars.add_get_values(&mut smt);

        // -----------------------------------------------------------------------------------------
        // Create Query
        // -----------------------------------------------------------------------------------------

        // wrap the query into a push/pop block
        let mut smtctx = Smt2Context::new();
        smtctx.subsection(format!("Verification of {}", m_op.ident()));
        // smtctx.comment(goal_expr_str);
        smtctx.level(smt);

        // create a new query from the smt context
        let mut query = Z3Query::from(smtctx);
        query.set_program(prog).set_goal(goal_str);

        if !symvars.is_empty() && goal_expr.has_translate_range() {
            // println!("MAKING QUERY COMPLEX\n");
            query.set_complex();
        }

        Box::new(query)
    }

    /// submits one query to the z3 worker pool
    pub fn submit_one(&mut self, z3: &mut Z3WorkerPool) -> bool {
        self.do_submit(z3, Some(1))
    }

    /// submits all queries to the z3 worker pool
    pub fn submit_all(&mut self, z3: &mut Z3WorkerPool) -> bool {
        self.do_submit(z3, None)
    }

    /// submits the supplied number of elements from the queue
    pub fn submit_n(&mut self, z3: &mut Z3WorkerPool, num: usize) -> bool {
        self.do_submit(z3, Some(num))
    }

    /// submits `num` queries to the Z3 worker pool
    pub fn submit(&mut self, z3: &mut Z3WorkerPool) -> bool {
        self.do_submit(z3, Some(self.batch_size))
    }

    /// processes the results of the submitted queries
    pub fn process_results(&mut self, z3: &mut Z3WorkerPool) -> bool {
        self.do_check_submitted(z3);
        !self.completed.is_empty()
    }

    /// handles submitting up `num` queries to the verifier, if None all ready queries are submitted
    fn do_submit(&mut self, z3: &mut Z3WorkerPool, num: Option<usize>) -> bool {
        if self.queries_done {
            return false;
        }
        let mut has_submitted = false;
        loop {
            // check the supplied limit
            if let Some(num) = num {
                if self.submitted.len() >= num {
                    // we've reached the limit of queries to be submitted, let's return
                    // true if we have submitted anything or we know that we're not done
                    return has_submitted || !self.queries_done;
                }
            }

            // try to submit equeries to the verifier
            match self.programs.next(z3) {
                MaybeResult::Some(prog) => {
                    // we got a new query to submit, try submitting it to the solver and
                    // record that we've submitted a query
                    has_submitted = true;

                    let query = self.to_smt_query(prog);
                    match z3.submit_query(query, self.priority) {
                        Ok(ticket) => {
                            self.stat_num_queries += 1;
                            self.submitted.push_back(ticket)
                        }
                        Err(e) => panic!("Error submitting query: {}", e),
                    }
                }
                MaybeResult::Pending => {
                    // we can submit more queries, but the queries are not ready yet
                    // returning true indicating there is some more work to be done
                    return true;
                }
                MaybeResult::None => {
                    // we've exhausted the queries, set the queries done flag and return
                    // whether we've submitted any new queries
                    self.queries_done = true;
                    return has_submitted;
                }
            }
        }
    }

    /// checks the submitted queries for results
    fn do_check_submitted(&mut self, z3: &mut Z3WorkerPool) {
        if self.submitted.is_empty() {
            return;
        }

        let mut submitted = LinkedList::new();
        while let Some(ticket) = self.submitted.pop_front() {
            if let Some(mut result) = z3.get_result(ticket) {
                let mut program = result.query_mut().take_program().unwrap();
                let output = result.result();
                match utils::check_result(output, &mut program) {
                    utils::QueryResult::Sat => {
                        self.stat_num_sat += 1;
                        self.completed.push_back(program);
                    }
                    utils::QueryResult::Unknown => {
                        // see to insert that again...
                        // panic!("huh???");
                        // println!("timeout! {ticket} resubmitting query...");
                        let mut query = result.take_query().unwrap();
                        query.set_program(program);
                        drop(result);
                        // let query = self.to_smt_query(program);
                        match z3.resubmit_query(query, self.priority) {
                            Ok(ticket) => {
                                // self.stat_num_queries += 1; // it's the same query!
                                submitted.push_back(ticket)
                            }
                            Err(e) => panic!("Error submitting query: {}", e),
                        }
                    }
                    utils::QueryResult::Error => {
                        self.queries_done = true;
                        self.submitted.clear();
                        self.completed.clear();
                        log::error!("Error in query: {}", result);
                        return;
                    }
                    _ => (),
                }
            } else {
                submitted.push_back(ticket);
            }
        }

        // update the submitted list
        self.submitted = submitted;
    }
}

impl ProgramBuilder for ProgramVerifier {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        self.do_check_submitted(z3);

        if let Some(p) = self.completed.pop_front() {
            // if we don't have anything here, submit a batch of queries
            if self.completed.is_empty() {
                self.do_submit(z3, Some(self.batch_size));
            }
            return MaybeResult::Some(p);
        }

        let pending = self.do_submit(z3, Some(self.batch_size));
        if self.submitted.is_empty() && !pending {
            assert!(self.queries_done || self.programs.next(z3) == MaybeResult::None);
            MaybeResult::None
        } else {
            MaybeResult::Pending
        }
    }

    /// returns an estimate of the number of programs
    fn size_hint(&self) -> (u128, Option<u128>) {
        self.programs.size_hint()
    }

    fn m_op(&self) -> &VelosiAstMethod {
        self.programs.m_op()
    }

    fn assms(&self) -> Rc<Vec<Term>> {
        self.programs.assms()
    }

    fn goal_expr(&self) -> Rc<VelosiAstExpr> {
        self.programs.goal_expr()
    }

    fn do_fmt(&self, f: &mut Formatter<'_>, indent: usize, debug: bool) -> FmtResult {
        let i = " ".repeat(indent);
        writeln!(
            f,
            "{i} ? ProgramVerifier ({} / {}) prio: {}, batch: {}",
            self.stat_num_sat, self.stat_num_queries, self.priority, self.batch_size
        )?;
        self.programs.do_fmt(f, indent + 2, debug)
    }

    fn set_priority(&mut self, priority: Z3TaskPriority) {
        self.priority = priority;
        self.programs.set_priority(priority.lower());
    }
}

/// Implement `From` for `ProgramVerifier
///
/// To allow conversions from ProgramVerifier -> Box<dyn ProgramBuilder>
impl From<ProgramVerifier> for Box<dyn ProgramBuilder> {
    fn from(q: ProgramVerifier) -> Self {
        Box::new(q)
    }
}

impl Display for ProgramVerifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, false)
    }
}

impl Debug for ProgramVerifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, true)
    }
}
