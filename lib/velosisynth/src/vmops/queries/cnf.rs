// Velosiraptor Synthesizer
//
//
// MIT License
//
// Copyright (c) 2022,2023 Systopia Lab, Computer Science, University of British Columbia
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

// std imports
use std::collections::LinkedList;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use smt2::Term;
use velosiast::{
    ast::{
        VelosiAstBinOp, VelosiAstBinOpExpr, VelosiAstBoolLiteralExpr, VelosiAstExpr,
        VelosiAstMethod, VelosiAstUnOpExpr, VelosiAstUnitSegment,
    },
    VelosiTokenStream,
};

use crate::{
    z3::{Z3TaskPriority, Z3WorkerPool},
    Program,
};

//use super::queryhelper::{MaybeResult, ProgramBuilder, QueryBuilder};
use super::MaybeResult;
use super::{BoolExprQueryBuilder, ProgramVerifier, DEFAULT_BATCH_SIZE};

use super::ProgramBuilder;

// use crate::ProgramsIter;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Single Boolean Expression Queries
////////////////////////////////////////////////////////////////////////////////////////////////////

// Some dummy implementatin for now...
use crate::ProgramsIter;
impl ProgramBuilder for ProgramsIter {
    fn next(&mut self, _z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        self.programs.pop().into()
    }

    fn m_op(&self) -> &VelosiAstMethod {
        panic!("m_op shoud not be called on ProgramsIter!")
    }

    /// the assumptions for the program
    fn assms(&self) -> Rc<Vec<Term>> {
        panic!("assms shoud not be called on ProgramsIter")
    }

    /// the expression that the program needs to establish
    fn goal_expr(&self) -> Rc<VelosiAstExpr> {
        panic!("goal_expr shoud not be called on ProgramsIter")
    }

    fn do_fmt(&self, f: &mut Formatter<'_>, indent: usize, debug: bool) -> FmtResult {
        let i = " ".repeat(indent);
        writeln!(
            f,
            "{i}  + ProgramsIter (num: {} / {})",
            self.stat_num_programs - self.programs.len(),
            self.stat_num_programs
        )?;
        Ok(())
    }
}

/// Implement `From` for `ProgramsIter`
///
/// To allow conversions from ProgramsIter -> Box<dyn ProgramBuilder>
impl From<ProgramsIter> for Box<dyn ProgramBuilder> {
    fn from(q: ProgramsIter) -> Self {
        Box::new(q)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Compound Query Builder
////////////////////////////////////////////////////////////////////////////////////////////////////

enum PartialPrograms {
    None,
    Verified(Vec<Box<dyn ProgramBuilder>>),
    All(Vec<Box<dyn ProgramBuilder>>),
}

pub struct CompoundBoolExprQueryBuilder<'a> {
    /// the unit context for this query
    unit: &'a VelosiAstUnitSegment,
    /// the operation we want to synthesize (map/protect/unmap)
    m_op: Rc<VelosiAstMethod>,
    /// the expressions to operate on
    exprs: Vec<Rc<VelosiAstExpr>>,
    /// partial programs for
    partial_programs: PartialPrograms,
    /// the assumptions we want to use
    assms: Vec<Term>,
    /// whether or not to negate the preconditino
    negate: bool,
    /// whether we want to be order preserving or not
    order_preserving: bool,
    /// the size of the batch
    batchsize: usize,
    /// the priority of the subqueries
    priority: Z3TaskPriority,
}

impl<'a> CompoundBoolExprQueryBuilder<'a> {
    pub fn new(unit: &'a VelosiAstUnitSegment, m_op: Rc<VelosiAstMethod>) -> Self {
        Self {
            unit,
            m_op,
            exprs: Vec::new(),
            assms: Vec::new(),
            negate: false,
            partial_programs: PartialPrograms::None,
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

    /// sets partial programs to supplied vector
    pub fn partial_programs(
        mut self,
        programs: Vec<Box<dyn ProgramBuilder>>,
        verify: bool,
    ) -> Self {
        self.partial_programs = if !verify {
            PartialPrograms::Verified(programs)
        } else {
            PartialPrograms::All(programs)
        };
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

    pub fn order_preserving(mut self) -> Self {
        self.order_preserving = true;
        self
    }

    pub fn priority(mut self, priority: Z3TaskPriority) -> Self {
        self.priority = priority;
        self
    }

    /// sets the base query to be all (i.e., A && B && C)
    pub fn all(self) -> Option<CompoundBoolExprQuery> {
        let assms = Rc::new(self.assms);
        let prefix = self.unit.ident();

        // no partial programs, simply take the expressions and build the query
        let mut candidate_programs = Vec::with_capacity(self.exprs.len());
        let mut exprs = Vec::new();
        match self.partial_programs {
            PartialPrograms::All(pb) => {
                let batch_size = self.batchsize;
                let priority = self.priority;
                candidate_programs = pb
                    .into_iter()
                    .map(|p| {
                        exprs.push(p.goal_expr());
                        ProgramVerifier::with_batchsize(prefix.clone(), p, batch_size, priority)
                            .into()
                    })
                    .collect();
            }
            PartialPrograms::Verified(pb) => {
                exprs = pb.iter().map(|p| p.goal_expr()).collect();
                candidate_programs = pb;
            }
            PartialPrograms::None => {
                for expr in self.exprs.iter() {
                    let bool_expr_query =
                        BoolExprQueryBuilder::new(self.unit, self.m_op.clone(), expr.clone())
                            .assms(assms.clone())
                            .negate(self.negate)
                            .build();
                    if let Some(bool_expr_query) = bool_expr_query {
                        candidate_programs.push(
                            ProgramVerifier::with_batchsize(
                                prefix.clone(),
                                Box::new(bool_expr_query),
                                self.batchsize,
                                self.priority,
                            )
                            .into(),
                        );
                    }
                    exprs.push(expr.clone());
                }
            }
        }

        if candidate_programs.is_empty() {
            return None;
        }

        if self.negate {
            // this is !(A && B && C), we convert this to !A || !B || !C
            let partial_programs = exprs.iter().map(|_| LinkedList::new()).collect();
            let done = candidate_programs.iter().map(|_| false).collect();

            // negate the the expressions
            let exprs = exprs
                .into_iter()
                .map(|e| Rc::new(VelosiAstUnOpExpr::new_neg(e)))
                .collect();

            let compound_query = CompoundQueryAny {
                m_op: self.m_op,
                exprs,
                assms,
                candidate_programs,
                done,
                all_done: false,
                order_preserving: self.order_preserving,
                partial_programs,
            };

            Some(CompoundBoolExprQuery::Any(compound_query))
        } else {
            // this is A && B && C, keep it that way

            const DEFAULT_CHUNK_SIZE: usize = 2;
            let mut queries = Vec::with_capacity(exprs.len() / DEFAULT_CHUNK_SIZE + 1);

            while candidate_programs.len() > DEFAULT_CHUNK_SIZE + (DEFAULT_CHUNK_SIZE / 2) {
                let cp = candidate_programs.split_off(DEFAULT_CHUNK_SIZE);
                let exp = exprs.split_off(DEFAULT_CHUNK_SIZE);

                let done = candidate_programs.iter().map(|_| false).collect();
                let partial_program_idx = candidate_programs.iter().map(|_| 0).collect();
                let partial_programs = candidate_programs.iter().map(|_| Vec::new()).collect();

                let compound_query = CompoundQueryAll {
                    m_op: self.m_op.clone(),
                    exprs,
                    assms: assms.clone(),
                    candidate_programs,
                    partial_programs,
                    partial_program_idx,
                    done,
                    partial_program_counter: 0,
                    all_done: false,
                };

                queries.push(CompoundBoolExprQuery::All(compound_query));

                candidate_programs = cp;
                exprs = exp;
            }

            let done = candidate_programs.iter().map(|_| false).collect();
            let partial_program_idx = candidate_programs.iter().map(|_| 0).collect();
            let partial_programs = candidate_programs.iter().map(|_| Vec::new()).collect();

            let compound_query = CompoundQueryAll {
                m_op: self.m_op.clone(),
                exprs,
                assms: assms.clone(),
                candidate_programs,
                partial_programs,
                partial_program_idx,
                done,
                partial_program_counter: 0,
                all_done: false,
            };

            queries.push(CompoundBoolExprQuery::All(compound_query));

            let batch_size = self.batchsize;

            loop {
                let mut queries_new = Vec::with_capacity(queries.len() / DEFAULT_CHUNK_SIZE + 1);
                if queries.len() == 1 {
                    break;
                }

                assert!(!queries.is_empty());

                while queries.len() > DEFAULT_CHUNK_SIZE + (DEFAULT_CHUNK_SIZE / 2) {
                    let cp = queries.split_off(DEFAULT_CHUNK_SIZE);

                    let done = queries.iter().map(|_| false).collect();
                    let partial_program_idx = queries.iter().map(|_| 0).collect();
                    let partial_programs = queries.iter().map(|_| Vec::new()).collect();
                    let exprs = queries.iter().map(|e| e.goal_expr()).collect();

                    let batch_size = self.batchsize;
                    let priority = self.priority;

                    let candidate_programs = queries
                        .into_iter()
                        .map(|p| {
                            ProgramVerifier::with_batchsize(
                                prefix.clone(),
                                Box::new(p),
                                batch_size,
                                priority,
                            )
                            .into()
                        })
                        .collect();

                    let compound_query = CompoundQueryAll {
                        m_op: self.m_op.clone(),
                        exprs,
                        assms: assms.clone(),
                        candidate_programs,
                        partial_programs,
                        partial_program_idx,
                        done,
                        partial_program_counter: 0,
                        all_done: false,
                    };

                    queries_new.push(CompoundBoolExprQuery::All(compound_query));
                    queries = cp;
                }

                let done = queries.iter().map(|_| false).collect();
                let partial_program_idx = queries.iter().map(|_| 0).collect();
                let partial_programs = queries.iter().map(|_| Vec::new()).collect();
                let exprs = queries.iter().map(|e| e.goal_expr()).collect();

                let batch_size = self.batchsize;
                let priority = self.priority;

                let candidate_programs = queries
                    .into_iter()
                    .map(|p| {
                        ProgramVerifier::with_batchsize(
                            prefix.clone(),
                            Box::new(p),
                            batch_size,
                            priority,
                        )
                        .into()
                    })
                    .collect();

                let compound_query = CompoundQueryAll {
                    m_op: self.m_op.clone(),
                    exprs,
                    assms: assms.clone(),
                    candidate_programs,
                    partial_programs,
                    partial_program_idx,
                    done,
                    partial_program_counter: 0,
                    all_done: false,
                };

                queries_new.push(CompoundBoolExprQuery::All(compound_query));

                queries = queries_new;
            }

            // let compound_query = CompoundQueryAll {
            //     m_op: self.m_op,
            //     exprs,
            //     assms,
            //     candidate_programs,
            //     partial_programs,
            //     partial_program_idx,
            //     done,
            //     partial_program_counter: 0,
            //     all_done: false,
            // };
            debug_assert_eq!(queries.len(), 1);
            queries.pop()
        }
    }

    /// sets the base query to be any (i.e., A || B || C)
    pub fn any(self) -> CompoundBoolExprQuery {
        let assms = Rc::new(self.assms);
        let prefix = self.unit.ident();

        // no partial programs, simply take the expressions and build the query
        let mut candidate_programs = Vec::with_capacity(self.exprs.len());
        let mut exprs = Vec::new();
        match self.partial_programs {
            PartialPrograms::All(pb) => {
                let batch_size = self.batchsize;
                let priority = self.priority;
                candidate_programs = pb
                    .into_iter()
                    .map(|p| {
                        exprs.push(p.goal_expr());
                        ProgramVerifier::with_batchsize(prefix.clone(), p, batch_size, priority)
                            .into()
                    })
                    .collect();
            }
            PartialPrograms::Verified(pb) => {
                exprs = pb.iter().map(|p| p.goal_expr()).collect();
                candidate_programs = pb;
            }
            PartialPrograms::None => {
                for expr in self.exprs.into_iter() {
                    let bool_expr_query =
                        BoolExprQueryBuilder::new(self.unit, self.m_op.clone(), expr.clone())
                            .assms(assms.clone())
                            .negate(self.negate)
                            .build();
                    if let Some(bool_expr_query) = bool_expr_query {
                        candidate_programs.push(
                            ProgramVerifier::with_batchsize(
                                prefix.clone(),
                                Box::new(bool_expr_query),
                                self.batchsize,
                                self.priority,
                            )
                            .into(),
                        );
                    }
                    exprs.push(expr);
                }
            }
        }

        let done = candidate_programs.iter().map(|_| false).collect();

        if self.negate {
            // this is !(A || B || C), we convert this to !A && !B && !C

            let partial_program_idx = candidate_programs.iter().map(|_| 0).collect();
            let partial_programs = candidate_programs.iter().map(|_| Vec::new()).collect();

            let compound_query = CompoundQueryAll {
                m_op: self.m_op,
                exprs,
                assms,
                candidate_programs,
                partial_programs,
                partial_program_idx,
                partial_program_counter: 0,
                done,
                all_done: false,
            };

            CompoundBoolExprQuery::All(compound_query)
        } else {
            // this is A || B || C, keep it that way

            let partial_programs = exprs.iter().map(|_| LinkedList::new()).collect();

            // this is !(A && B && C), we convert this to !A || !B || !C
            let compound_query = CompoundQueryAny {
                m_op: self.m_op,
                exprs,
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

////////////////////////////////////////////////////////////////////////////////////////////////////
// CNF Queries
////////////////////////////////////////////////////////////////////////////////////////////////////

pub enum CompoundBoolExprQuery {
    Any(CompoundQueryAny),
    All(CompoundQueryAll),
}

impl ProgramBuilder for CompoundBoolExprQuery {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        match self {
            Self::Any(q) => q.next(z3),
            Self::All(q) => q.next(z3),
        }
    }
    fn assms(&self) -> Rc<Vec<Term>> {
        match self {
            Self::Any(q) => q.assms(),
            Self::All(q) => q.assms(),
        }
    }

    fn goal_expr(&self) -> Rc<VelosiAstExpr> {
        match self {
            Self::Any(q) => q.goal_expr(),
            Self::All(q) => q.goal_expr(),
        }
    }

    fn m_op(&self) -> &VelosiAstMethod {
        match self {
            Self::Any(q) => q.m_op(),
            Self::All(q) => q.m_op(),
        }
    }

    fn mem_model(&self) -> bool {
        match self {
            Self::Any(q) => q.mem_model(),
            Self::All(q) => q.mem_model(),
        }
    }

    fn do_fmt(&self, f: &mut Formatter<'_>, indent: usize, debug: bool) -> FmtResult {
        match self {
            Self::Any(q) => q.do_fmt(f, indent, debug),
            Self::All(q) => q.do_fmt(f, indent, debug),
        }
    }
}

/// Implement `From` for `CompoundBoolExprQuery`
///
/// To allow conversions from CompoundBoolExprQuery -> Box<dyn ProgramBuilder>
impl From<CompoundBoolExprQuery> for Box<dyn ProgramBuilder> {
    fn from(q: CompoundBoolExprQuery) -> Self {
        Box::new(q)
    }
}

impl Display for CompoundBoolExprQuery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, false)
    }
}

impl Debug for CompoundBoolExprQuery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, true)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
/// Disjunctive Normal Form
////////////////////////////////////////////////////////////////////////////////////////////////////

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

    fn assms(&self) -> Rc<Vec<Term>> {
        self.assms.clone()
    }

    fn goal_expr(&self) -> Rc<VelosiAstExpr> {
        match self.exprs.len() {
            0 => {
                // just taking true as the goal expression
                log::warn!("encountered empty compound query (ANY)");
                Rc::new(VelosiAstExpr::BoolLiteral(VelosiAstBoolLiteralExpr::btrue()))
            }
            1 => {
                // simply take the only expression we have
                self.exprs[0].clone()
            }
            _ => {
                let mut expr = self.exprs[0].clone();
                for e in self.exprs.iter().skip(1) {
                    if let VelosiAstExpr::BoolLiteral(be) = e.as_ref() {
                        if be.val {
                            log::warn!(
                                "encountered always true expression in compound query (ANY)"
                            );
                            // this one was true, which means the entire expression is always true
                            return e.clone();
                        } else {
                            // just skip the false one
                        }
                    } else {
                        expr = Rc::new(VelosiAstExpr::BinOp(VelosiAstBinOpExpr {
                            op: VelosiAstBinOp::Or,
                            lhs: expr,
                            rhs: e.clone(),
                            loc: VelosiTokenStream::default(),
                        }));
                    }
                }

                expr
            }
        }
    }

    fn m_op(&self) -> &VelosiAstMethod {
        self.m_op.as_ref()
    }

    fn do_fmt(&self, f: &mut Formatter<'_>, indent: usize, debug: bool) -> FmtResult {
        let i = " ".repeat(indent);
        writeln!(f, "{i} # CompoundQueryAny( assms )")?;
        if self.candidate_programs.is_empty() {
            writeln!(f, "{i}   - true")
        } else {
            for p in self.candidate_programs.iter() {
                p.do_fmt(f, indent + 4, debug)?;
            }
            Ok(())
        }
    }
}

/// Implement `From` for `CompoundQueryAny`
///
/// To allow conversions from CompoundQueryAny -> Box<dyn ProgramBuilder>
impl From<CompoundQueryAny> for Box<dyn ProgramBuilder> {
    fn from(q: CompoundQueryAny) -> Self {
        Box::new(q)
    }
}

impl Display for CompoundQueryAny {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, false)
    }
}

impl Debug for CompoundQueryAny {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, true)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
/// Conjunctive Normal Form
////////////////////////////////////////////////////////////////////////////////////////////////////

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
    /// how many partial programs we have
    partial_program_counter: usize,
    /// boolean flags indicating which candidate programs we've exhausted
    done: Vec<bool>,
    /// flag indicating whether we're all done
    all_done: bool,
}
impl CompoundQueryAll {}

impl ProgramBuilder for CompoundQueryAll {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        if self.all_done {
            return MaybeResult::None;
        }

        // loop over all program parts, and check if there is one next
        let mut programs_ready = true;

        for i in 0..self.partial_programs.len() {
            // nothing to be done here
            if self.done[i] {
                continue;
            }

            programs_ready &= !self.partial_programs[i].is_empty();

            // if we still have partial programs, we can skip that one
            if self.partial_program_idx[i] < self.partial_programs[i].len() {
                continue;
            }

            match self.candidate_programs[i].next(z3) {
                MaybeResult::Some(program) => self.partial_programs[i].push(program),
                MaybeResult::Pending => (),
                MaybeResult::None => {
                    debug_assert!(!self.done[i]);
                    self.done[i] = true;
                }
            }
        }

        // if we are the first and we had pending, return as we can't do anyting yet
        if self.partial_program_counter == 0 && !programs_ready {
            return MaybeResult::Pending;
        }

        // create a snapshot of current, as we may need to roll back
        let partial_program_idx = self.partial_program_idx.clone();

        // increment the current index
        let mut carry = true;
        let mut had_pending = false;
        let mut had_none = false;
        for i in 0..self.partial_programs.len() {
            if carry {
                debug_assert!(!self.partial_programs[i].is_empty());
                debug_assert!(self.partial_program_idx[i] < self.partial_programs[i].len());
                // carry flag indicating that we need to increment the current position
                self.partial_program_idx[i] += 1;
                if self.partial_program_idx[i] == self.partial_programs[i].len() {
                    if !self.done[i] {
                        // the current program is not done yet, we try to see if there is another
                        // program available for that part
                        match self.candidate_programs[i].next(z3) {
                            MaybeResult::Some(program) => {
                                // add the program to the list of partial programs and clear the
                                // carry flag as we just incremented the current position. Meaning
                                // that self.partial_program_idx[i] != self.partial_programs[i].len()
                                self.partial_programs[i].push(program);
                                carry = false;
                            }
                            MaybeResult::Pending => {
                                // we are still pending, so we can just return pending and break
                                // out of the loop here
                                self.partial_program_idx = partial_program_idx;
                                return MaybeResult::Pending;
                            }
                            MaybeResult::None => {
                                // the current program is done now, so we can set the done flag
                                debug_assert!(!self.done[i]);
                                self.done[i] = true;
                            }
                        }
                    }

                    // we reached the end of the available programs for the current position
                    if self.done[i] {
                        // we're done. we simply reset the current index, and continue with the
                        // carry bit set.
                        self.partial_program_idx[i] = 0;
                    }
                } else {
                    // no wrap around, so there is no carry here
                    carry = false;
                }
            }

            if self.partial_programs[i].is_empty() {
                log::warn!(
                    "Programs {} / {} is empty current idx: {}",
                    i,
                    self.partial_programs.len(),
                    self.partial_program_counter
                );
            }

            had_none |= self.partial_programs[i].is_empty();
        }

        if had_pending {
            // roll back the current
            self.partial_program_idx = partial_program_idx;
            return MaybeResult::Pending;
        }

        if had_none {
            self.all_done = true;
            log::warn!("one of the programs was empty!");
            return MaybeResult::None;
        }

        self.partial_program_counter += 1;

        if carry {
            self.all_done = true;
        }

        log::debug!(
            "Program Idx: {:?} {}",
            partial_program_idx
                .iter()
                .map(|i| *i as usize)
                .collect::<Vec<_>>(),
            self.partial_program_counter
        );

        let prog = partial_program_idx
            .iter()
            .enumerate()
            .fold(Program::new(), |prog, (i, e)| {
                prog.merge(&self.partial_programs[i][*e].clone())
            });

        MaybeResult::Some(prog)
    }

    fn m_op(&self) -> &VelosiAstMethod {
        self.m_op.as_ref()
    }

    fn assms(&self) -> Rc<Vec<Term>> {
        self.assms.clone()
    }

    fn goal_expr(&self) -> Rc<VelosiAstExpr> {
        match self.exprs.len() {
            0 => {
                // just taking true as the goal expression
                log::warn!("encountered empty compound query (ALL)");
                Rc::new(VelosiAstExpr::BoolLiteral(VelosiAstBoolLiteralExpr::btrue()))
            }
            1 => {
                // simply take the only expression we have
                self.exprs[0].clone()
            }
            _ => {
                let mut expr = self.exprs[0].clone();
                for e in self.exprs.iter().skip(1) {
                    if let VelosiAstExpr::BoolLiteral(be) = e.as_ref() {
                        if !be.val {
                            log::warn!(
                                "encountered always false expression in compound query (ALL)"
                            );
                            // this one was true, which means the entire expression is always true
                            return e.clone();
                        } else {
                            // just skip the true one
                        }
                    } else {
                        expr = Rc::new(VelosiAstExpr::BinOp(VelosiAstBinOpExpr {
                            op: VelosiAstBinOp::Land,
                            lhs: expr,
                            rhs: e.clone(),
                            loc: VelosiTokenStream::default(),
                        }));
                    }
                }

                expr
            }
        }
    }

    fn do_fmt(&self, f: &mut Formatter<'_>, indent: usize, debug: bool) -> FmtResult {
        let i = " ".repeat(indent);
        writeln!(f, "{i} # CompoundQueryAll( assms ==> {})", self.goal_expr())?;
        if self.candidate_programs.is_empty() {
            writeln!(f, "{i}   - true")
        } else {
            for p in self.candidate_programs.iter() {
                p.do_fmt(f, indent + 4, debug)?;
            }
            Ok(())
        }
    }
}

/// Implement `From` for `CompoundQueryAll`
///
/// To allow conversions from CompoundQueryAll -> Box<dyn ProgramBuilder>
impl From<CompoundQueryAll> for Box<dyn ProgramBuilder> {
    fn from(q: CompoundQueryAll) -> Self {
        Box::new(q)
    }
}

impl Display for CompoundQueryAll {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, false)
    }
}

impl Debug for CompoundQueryAll {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, true)
    }
}
