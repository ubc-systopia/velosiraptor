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

//! Handles Conjunctive Normal Form

use std::collections::{HashSet, LinkedList};
use std::rc::Rc;

use smt2::{Smt2Context, SortedVar, Term};
use velosiast::ast::{VelosiAstExpr, VelosiAstMethod, VelosiAstUnitSegment};

use crate::{
    model::expr::expr_to_smt2,
    model::method::{call_method, call_method_assms, combine_method_params},
    model::types,
    z3::{Z3Query, Z3TaskPriority, Z3Ticket, Z3WorkerPool},
    Program,
};

use super::queryhelper::{MaybeResult, ProgramBuilder, QueryBuilder};

// use crate::ProgramsIter;

use super::utils;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Single Boolean Expression Queries
////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct BoolExprQueryBuilder<'a> {
    /// the unit context for this query
    unit: &'a VelosiAstUnitSegment,
    /// the programs that this query builder handles
    expr: Rc<VelosiAstExpr>,
    /// the operation method
    m_op: Rc<VelosiAstMethod>,
    /// assumptions for the boolean expressions
    assms: Rc<Vec<Term>>,
    /// whether or not to negate the expression
    negate: bool,
    /// whether to use the memory model
    mem_model: bool,
    /// whether or not to allow variable references
    variable_references: bool,
    /// the size of the batch
    batchsize: usize,
}

impl<'a> BoolExprQueryBuilder<'a> {
    /// creates a builder for boolean expression queries
    pub fn new(
        unit: &'a VelosiAstUnitSegment,
        expr: Rc<VelosiAstExpr>,
        m_op: Rc<VelosiAstMethod>,
    ) -> Self {
        Self {
            unit,
            expr,
            m_op,
            assms: Rc::new(Vec::new()),
            negate: false,
            mem_model: false,
            variable_references: false,
            batchsize: 1,
        }
    }

    /// sets the assumptions for the supplied vector
    pub fn assms(mut self, assms: Rc<Vec<Term>>) -> Self {
        self.assms = assms;
        self
    }

    /// whether or not to negate the conjunct
    pub fn negate(mut self, toggle: bool) -> Self {
        self.negate = toggle;
        self
    }

    /// sets the memory model to be used
    pub fn mem_model(mut self, toggle: bool) -> Self {
        self.mem_model = toggle;
        self
    }

    /// whether we want to allow variable references in the pre-conditions
    pub fn variable_references(mut self) -> Self {
        self.variable_references = true;
        self
    }

    /// the batch size to be used when submitting queries
    pub fn batchsize(mut self, batchsize: usize) -> Self {
        self.batchsize = batchsize;
        self
    }

    /// builds the bool expr query or returns None if there are no queries to be run
    pub fn build(self) -> Option<BoolExprQuery> {
        let mut params = HashSet::new();

        // if the expression doesn't have state references, then nothing to be done.
        if !self.expr.has_state_references() {
            return None;
        }

        // check if the expression has variable references and we want variable referenes
        if self.expr.has_var_references(&params) == self.variable_references {
            return None;
        }

        // Now we can generate the programs
        let programs =
            utils::make_program_builder(self.unit, self.m_op.as_ref(), &self.expr).into_iter();
        if !programs.has_programs() {
            return None;
        }

        Some(BoolExprQuery {
            programs: Box::new(programs),
            m_op: self.m_op,
            assms: self.assms,
            expr: self.expr,
            negate: self.negate,
            mem_model: self.mem_model,
        })
    }
}

pub struct BoolExprQuery {
    /// the programs that this query builder handles
    programs: Box<dyn ProgramBuilder>,
    /// the operation method
    m_op: Rc<VelosiAstMethod>,
    /// assumptions for the term
    assms: Rc<Vec<Term>>,
    /// the boolean expression to be evaluated
    expr: Rc<VelosiAstExpr>,
    /// whether or not to negate the expression
    negate: bool,
    /// whether to use the memory model
    mem_model: bool,
}

impl BoolExprQuery {
    fn to_smt_query(&self, prog: Program) -> Box<Z3Query> {
        // convert the program to a smt2 term
        let (mut smt, symvars) = prog.to_smt2_term(
            self.m_op.ident(),
            self.m_op.params.as_slice(),
            self.mem_model,
        );

        // build up the pre-conditions
        let pre1 = call_method_assms(&self.m_op, "st!0");
        let mut pre = self
            .assms
            .iter()
            .fold(pre1, |acc, assm| Term::land(acc, assm.clone()));
        if self.mem_model {
            pre = utils::add_empty_wbuffer_precond(pre);
        }

        let m_op_call = call_method(&self.m_op, vec![Term::from("st!0")]);

        // obtain the forall params
        let stvar = SortedVar::new("st!0".to_string(), types::model());
        let vars = combine_method_params(vec![stvar], self.m_op.params.as_slice(), &[]);

        // build the forall term for the query
        let t = if self.negate {
            Term::forall(vars, Term::lnot(expr_to_smt2(&self.expr, "st!0")))
        } else {
            Term::forall(vars, expr_to_smt2(&self.expr, "st!0"))
        };

        // get the goal string for the query
        let goal_str = t.to_string();

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
        query.set_program(prog).set_goal(goal_str);

        Box::new(query)
    }
}

impl QueryBuilder for BoolExprQuery {
    /// returns the next query to be submitted, or None if all have been submitted
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Box<Z3Query>> {
        match self.programs.next(z3) {
            MaybeResult::Some(prog) => MaybeResult::Some(self.to_smt_query(prog)),
            MaybeResult::Pending => MaybeResult::Pending,
            MaybeResult::None => MaybeResult::None,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// ProgramQueries
////////////////////////////////////////////////////////////////////////////////////////////////////

/// the default batch size
const DEFAULT_BATCH_SIZE: usize = 5;

pub struct QueryVerifier {
    /// sequence of queries to be submitted
    queries: Box<dyn QueryBuilder>,
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
}

impl QueryVerifier {
    /// creates a new query verifier for the queries with the given priority
    pub fn new(queries: Box<dyn QueryBuilder>, priority: Z3TaskPriority) -> Self {
        Self::with_batchsize(queries, 5, priority)
    }

    /// creates a new query verifier for the queries with the given priority and batch size
    pub fn with_batchsize(
        queries: Box<dyn QueryBuilder>,
        batch_size: usize,
        priority: Z3TaskPriority,
    ) -> Self {
        let batch_size = std::cmp::max(batch_size, 1);
        QueryVerifier {
            queries,
            priority,
            submitted: LinkedList::new(),
            completed: LinkedList::new(),
            batch_size,
            queries_done: false,
        }
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
        self.completed.len() > 0
    }

    /// handles submitting up `num` queries to the verifier, if None all ready queries are submitted
    fn do_submit(&mut self, z3: &mut Z3WorkerPool, num: Option<usize>) -> bool {
        let mut has_submitted = false;
        loop {
            // check the supplied limit
            if let Some(num) = num {
                if self.submitted.len() >= 2 * num {
                    // we've reached the limit of queries to be submitted, let's return
                    // true if we have submitted anything or we know that we're not done
                    return has_submitted || !self.queries_done;
                }
            }

            // try to submit equeries to the verifier
            match self.queries.next(z3) {
                MaybeResult::Some(query) => {
                    // we got a new query to submit, try submitting it to the solver and
                    // record that we've submitted a query
                    has_submitted = true;
                    match z3.submit_query(query, self.priority) {
                        Ok(ticket) => self.submitted.push_back(ticket),
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
                if utils::check_result(output, &mut program) == utils::QueryResult::Sat {
                    self.completed.push_back(program);
                }
            } else {
                submitted.push_back(ticket);
            }
        }

        // update the submitted list
        self.submitted = submitted;
    }
}

impl ProgramBuilder for QueryVerifier {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        self.do_check_submitted(z3);
        let pending = self.do_submit(z3, Some(self.batch_size));

        if let Some(p) = self.completed.pop_front() {
            MaybeResult::Some(p)
        } else if self.submitted.is_empty() && !pending {
            assert!(self.queries.next(z3) == MaybeResult::None);
            MaybeResult::None
        } else {
            MaybeResult::Pending
        }
    }
}

impl From<QueryVerifier> for Box<dyn ProgramBuilder> {
    fn from(q: QueryVerifier) -> Self {
        Box::new(q)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// CNF Queries
////////////////////////////////////////////////////////////////////////////////////////////////////

pub enum CompoundBoolExprQuery {
    Any(CompoundQueryAny),
    All(CompoundQueryAll),
}

pub struct CNFQueryBuilder<'a> {
    /// the unit context for this query
    unit: &'a VelosiAstUnitSegment,
    /// the operation we want to synthesize (map/protect/unmap)
    m_op: Rc<VelosiAstMethod>,
    /// the expressions to operate on
    exprs: Vec<Rc<VelosiAstExpr>>,
    /// the assumptions we want to use
    assms: Vec<Term>,
    /// whether or not to negate the preconditino
    negate: bool,
    /// whether to use the memory model
    mem_model: bool,
    /// whether we want to be order preserving or not
    order_preserving: bool,
    /// the size of the batch
    batchsize: usize,
    /// the priority of the subqueries
    priority: Z3TaskPriority,
}

impl<'a> CNFQueryBuilder<'a> {
    pub fn new(unit: &'a VelosiAstUnitSegment, m_op: Rc<VelosiAstMethod>) -> Self {
        Self {
            unit,
            m_op,
            exprs: Vec::new(),
            assms: Vec::new(),
            negate: false,
            mem_model: false,
            order_preserving: false,
            batchsize: DEFAULT_BATCH_SIZE,
            priority: Z3TaskPriority::Medium,
        }
    }

    /// sets the expressions to the supplied vector
    pub fn exprs(mut self, exprs: Vec<Rc<VelosiAstExpr>>) -> Self {
        self.exprs = exprs;
        self
    }

    /// adds an expression to the list
    pub fn add_expr(mut self, expr: Rc<VelosiAstExpr>) -> Self {
        self.exprs.push(expr);
        self
    }

    // sets the assumptions for the supplied vector
    pub fn assms(mut self, assms: Vec<Term>) -> Self {
        self.assms = assms;
        self
    }

    /// adds assumption for the terms
    pub fn add_assm(mut self, assm: Term) -> Self {
        self.assms.push(assm);
        self
    }

    /// whether or not to negate the conjunct
    pub fn negate(mut self) -> Self {
        self.negate = !self.negate;
        self
    }

    /// sets the memory model to be used
    pub fn mem_model(mut self) -> Self {
        self.mem_model = true;
        self
    }

    pub fn order_preserving(mut self) -> Self {
        self.order_preserving = true;
        self
    }

    pub fn priority(mut self, priority: Z3TaskPriority) -> Self {
        self.priority = priority;
        self
    }

    /// sets the base query to be all (i.e., A && B && C)
    pub fn all(mut self) -> CompoundBoolExprQuery {
        let assms = Rc::new(self.assms);

        let done = self.exprs.iter().map(|_| false).collect();

        let mut candidate_programs = Vec::with_capacity(self.exprs.len());
        for expr in self.exprs.iter() {
            let bool_expr_query =
                BoolExprQueryBuilder::new(self.unit, expr.clone(), self.m_op.clone())
                    .assms(assms.clone())
                    .negate(self.negate)
                    .mem_model(self.mem_model)
                    .build();
            if let Some(bool_expr_query) = bool_expr_query {
                candidate_programs.push(
                    QueryVerifier::with_batchsize(
                        Box::new(bool_expr_query),
                        self.batchsize,
                        self.priority,
                    )
                    .into(),
                );
            }
        }

        if self.negate {
            let partial_programs = self.exprs.iter().map(|_| LinkedList::new()).collect();

            // this is !(A && B && C), we convert this to !A || !B || !C
            let compound_query = CompoundQueryAny {
                m_op: self.m_op,
                exprs: self.exprs,
                assms,
                candidate_programs,
                done,
                all_done: false,
                order_preserving: self.order_preserving,
                partial_programs,
            };

            CompoundBoolExprQuery::Any(compound_query)
        } else {
            let partial_program_idx = candidate_programs.iter().map(|_| 0).collect();
            let partial_programs = candidate_programs.iter().map(|_| Vec::new()).collect();

            // this is A && B && C, keep it that way
            let compound_query = CompoundQueryAll {
                m_op: self.m_op,
                exprs: self.exprs,
                assms,
                candidate_programs,
                partial_programs,
                partial_program_idx,
                done,
                all_done: false,
            };

            CompoundBoolExprQuery::All(compound_query)
        }
    }

    /// sets the base query to be any (i.e., A || B || C)
    pub fn any(mut self) -> CompoundBoolExprQuery {
        let assms = Rc::new(self.assms);

        let done = self.exprs.iter().map(|_| false).collect();

        let mut candidate_programs = Vec::with_capacity(self.exprs.len());
        for expr in self.exprs.iter() {
            let bool_expr_query =
                BoolExprQueryBuilder::new(self.unit, expr.clone(), self.m_op.clone())
                    .assms(assms.clone())
                    .negate(self.negate)
                    .mem_model(self.mem_model)
                    .build();
            if let Some(bool_expr_query) = bool_expr_query {
                candidate_programs.push(
                    QueryVerifier::with_batchsize(
                        Box::new(bool_expr_query),
                        self.batchsize,
                        self.priority,
                    )
                    .into(),
                );
            }
        }

        if self.negate {
            // this is !(A || B || C), we convert this to !A && !B && !C

            let partial_program_idx = candidate_programs.iter().map(|_| 0).collect();
            let partial_programs = candidate_programs.iter().map(|_| Vec::new()).collect();

            let compound_query = CompoundQueryAll {
                m_op: self.m_op,
                exprs: self.exprs,
                assms,
                candidate_programs,
                partial_programs,
                partial_program_idx,
                done,
                all_done: false,
            };

            CompoundBoolExprQuery::All(compound_query)

        } else {
            // this is A || B || C, keep it that way

            let partial_programs = self.exprs.iter().map(|_| LinkedList::new()).collect();

            // this is !(A && B && C), we convert this to !A || !B || !C
            let compound_query = CompoundQueryAny {
                m_op: self.m_op,
                exprs: self.exprs,
                assms,
                candidate_programs,
                done,
                all_done: false,
                order_preserving: self.order_preserving,
                partial_programs,
            };
            CompoundBoolExprQuery::Any(compound_query)
        }
    }
}

pub struct CompoundQueryAny {
    /// the operation we want to synthesize (map/protect/unmap)
    m_op: Rc<VelosiAstMethod>,
    /// the expressions to operate on
    exprs: Vec<Rc<VelosiAstExpr>>,
    /// the assumptions we want to use
    assms: Rc<Vec<Term>>,
    /// generator for the candidate programs for each expression
    candidate_programs: Vec<Box<dyn ProgramBuilder>>,
    /// boolean flags indicating which candidate programs we've exhausted
    done: Vec<bool>,
    /// flag indicating whether we're all done
    all_done: bool,
    /// flag indicating whether we follow the priority
    order_preserving: bool,
    /// programs that satisfy the query
    partial_programs: Vec<LinkedList<Program>>,
}

impl CompoundQueryAny {}

impl ProgramBuilder for CompoundQueryAny {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        // nothing more to be done, so indicate this
        if self.all_done {
            return MaybeResult::None;
        }

        // set all_done flag to true, and clear it if we have more to process
        self.all_done = true;

        // loop over all candidate programs and find the ones that satisfy the query
        // return the first one we find, no matter the order
        let mut had_pending = false;
        for (i, cp) in self.candidate_programs.iter_mut().enumerate() {
            // if we have a partial program for this part, return it. This should be order preserving
            if !self.partial_programs[i].is_empty() {
                self.all_done = true;
                return MaybeResult::Some(self.partial_programs[i].pop_front().unwrap());
            }

            // if that part is done, we're checking with the next part
            if self.done[i] {
                continue;
            }
            self.all_done = true;

            match cp.next(z3) {
                MaybeResult::Some(program) => {
                    // if we need to preserve the order and we've seen a pending part already,
                    // then we push it back to the partial programs
                    if self.order_preserving && had_pending {
                        self.partial_programs[i].push_back(program);
                    } else {
                        return MaybeResult::Some(program);
                    }
                }
                MaybeResult::Pending => {
                    // we have a pending part, so record that. We'll just check the next
                    // part to see whether there's a program for that, or return pending if
                    // it's order preserving.
                    had_pending = true;
                }
                MaybeResult::None => {
                    // we know there is nothing more to come from that part, so we can set
                    // it to done.
                    self.done[i] = true;
                }
            }
        }

        if had_pending || !self.all_done {
            MaybeResult::Pending
        } else {
            MaybeResult::None
        }
    }

    // assms()
    // expr() -> Rc<VelosiAstExpr> or Term
}

pub struct CompoundQueryAll {
    /// the operation we want to synthesize (map/protect/unmap)
    m_op: Rc<VelosiAstMethod>,
    /// the expressions to operate on
    exprs: Vec<Rc<VelosiAstExpr>>,
    /// the assumptions we want to use
    assms: Rc<Vec<Term>>,
    /// generator for the candidate programs for each expression
    candidate_programs: Vec<Box<dyn ProgramBuilder>>,
    /// partial programs that satify one part of the query
    partial_programs: Vec<Vec<Program>>,
    /// index into the partial programs for combining
    partial_program_idx: Vec<usize>,
    /// boolean flags indicating which candidate programs we've exhausted
    done: Vec<bool>,
    /// flag indicating whether we're all done
    all_done: bool,
}
