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

use std::collections::VecDeque;

use super::utils;
use crate::vmops::precond::PrecondQueries;
use crate::vmops::semantics::SemanticQueries;
use crate::vmops::semprecond::SemPrecondQueries;
use crate::{Program, ProgramsIter};
use crate::{Z3Query, Z3TaskPriority, Z3Ticket, Z3WorkerPool};

#[derive(Clone, PartialEq, Eq)]
pub enum MaybeResult<T> {
    /// we have a result
    Some(T),
    /// the result is not yet available
    Pending,
    /// There are no results here, no programs that are being built
    None,
}

/// query builder trait that provides a squence of queries to be submitted to Z3
pub trait QueryBuilder {
    /// returns the next query to be submitted, or None if all have been submitted
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Box<Z3Query>>;
}

/// produces a new program
pub trait ProgramBuilder {
    /// returns the next query to be submitted, or None if all have been submitted
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program>;
}

pub enum PartQueries {
    Precond(PrecondQueries),
    Semantic(ProgramQueries<SemanticQueries>),
    SemPrecond(SemPrecondQueries),
}

impl ProgramBuilder for PartQueries {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        match self {
            Self::Precond(q) => q.next(z3),
            Self::Semantic(q) => q.next(z3),
            Self::SemPrecond(q) => q.next(z3),
        }
    }
}

/// keeps track of queries
pub struct ProgramQueries<T>
where
    T: QueryBuilder,
{
    /// sequence of queries to be submitted
    queries: T,
    ///
    priority: Z3TaskPriority,
    /// the submitted queries
    submitted: Vec<Z3Ticket>,
    /// programs that had SAT results
    completed: VecDeque<Program>,
    /// the batch size for submiting queries
    batch_size: usize,
}

impl<T> ProgramQueries<T>
where
    T: QueryBuilder,
{
    pub fn new(queries: T, priority: Z3TaskPriority) -> Self {
        Self::with_batchsize(queries, 5, priority)
    }

    pub fn with_batchsize(queries: T, batch_size: usize, priority: Z3TaskPriority) -> Self {
        let batch_size = std::cmp::min(batch_size, 1);
        ProgramQueries {
            queries,
            priority,
            submitted: Vec::with_capacity(batch_size),
            completed: VecDeque::with_capacity(batch_size),
            batch_size,
        }
    }

    // pub fn submit(&mut self, z3: &mut Z3WorkerPool) {
    //     self.maybe_submit(z3);
    // }

    fn maybe_submit(&mut self, z3: &mut Z3WorkerPool) -> bool {
        // don't submit more than the batch size, there may be other pending queries
        // if self.submitted.len() >= self.batch_size {
        //     return true;
        // }
        let mut pending = false;
        for _ in 0..self.batch_size {
            // get the next query and try to submit it
            match self.queries.next(z3) {
                MaybeResult::Some(query) => {
                    pending = true;
                    match z3.submit_query(query, self.priority) {
                        Ok(ticket) => self.submitted.push(ticket),
                        Err(e) => panic!("Error submitting query: {}", e),
                    }
                }
                MaybeResult::Pending => {
                    return true;
                }
                MaybeResult::None => {
                    return pending;
                }
            }
        }

        true
    }

    fn check_submitted(&mut self, z3: &mut Z3WorkerPool) -> bool {
        // submit queries, if it's pending and submitted is empty, return as we need to wait
        let has_pending = self.maybe_submit(z3);
        if self.submitted.is_empty() {
            return has_pending;
        }

        // get the new submitted array
        let mut submitted = Vec::with_capacity(self.submitted.len());

        // loop over all inflight queries
        for ticket in self.submitted.iter() {
            if let Some(mut result) = z3.get_result(*ticket) {
                let mut program = result.query_mut().take_program().unwrap();
                let output = result.result();
                if utils::check_result(output, &mut program) == utils::QueryResult::Sat {
                    self.completed.push_back(program);
                }
            } else {
                submitted.push(*ticket);
            }
        }

        self.submitted = submitted;

        // self.maybe_submit(z3)
        true
    }
}

impl<T> ProgramBuilder for ProgramQueries<T>
where
    T: QueryBuilder,
{
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        let pending = self.check_submitted(z3);

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

pub struct SequentialProgramQueries<T>
where
    T: ProgramBuilder,
{
    queries: Vec<T>,
    idx: usize,
}

impl<T> SequentialProgramQueries<T>
where
    T: ProgramBuilder,
{
    pub fn new(queries: Vec<T>) -> Self {
        Self { queries, idx: 0 }
    }
}

impl<T> ProgramBuilder for SequentialProgramQueries<T>
where
    T: ProgramBuilder,
{
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        // no more work to do
        if self.idx >= self.queries.len() {
            return MaybeResult::None;
        }

        match self.queries[self.idx].next(z3) {
            MaybeResult::None => {
                self.idx += 1;
                self.next(z3)
            }
            res => res,
        }
    }
}


///
pub struct MultiDimProgramQueries<T>
where
    T: ProgramBuilder,
{
    queries: Vec<T>,
    programs: Vec<Vec<Program>>,
    current: Vec<usize>,
    done: Vec<bool>,
    idx: usize,
    all_done: bool,
}

impl<T> MultiDimProgramQueries<T>
where
    T: ProgramBuilder,
{
    pub fn new(queries: Vec<T>) -> Self {
        let current = queries.iter().map(|_| 0).collect();
        let programs = queries.iter().map(|_| Vec::new()).collect();
        let done = queries.iter().map(|_| false).collect();
        Self {
            queries,
            programs,
            current,
            done,
            idx: 0,
            all_done: false,
        }
    }
}

impl<T> ProgramBuilder for MultiDimProgramQueries<T>
where
    T: ProgramBuilder,
{
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        if self.all_done {
            return MaybeResult::None;
        }

        // loop over all program parts, and check if there is one next
        let mut had_pending = false;

        for i in 0..self.programs.len() {
            if self.done[i] {
                continue;
            }

            match self.queries[i].next(z3) {
                MaybeResult::Some(program) => self.programs[i].push(program),
                // it's a pending result
                MaybeResult::Pending => {
                    // reset the pending, so we check again next turn, so we are not all done
                    had_pending = true;
                }
                MaybeResult::None => {
                    debug_assert!(!self.done[i]);
                    self.done[i] = true;
                }
            }
        }

        // if we are the first and we had pending, return as we can't do anyting yet
        if self.idx == 0 && had_pending {
            return MaybeResult::Pending;
        }

        // create a snapshot of current, as we may need to roll back
        let current = self.current.clone();

        // increment the current index
        let mut carry = true;
        let mut had_pending = false;
        let mut had_none = false;
        for i in 0..self.programs.len() {
            if carry {
                self.current[i] += 1;
                // if we have reached the end, and this one is not done this means it's pending
                if self.current[i] == self.programs[i].len() {
                    if self.done[i] {
                        self.current[i] = 0;
                    } else {
                        // here we had a pending query that we need.
                        had_pending = true;
                        break;
                    }
                } else {
                    // no wrap around, so there is no carry here
                    carry = false;
                }
            }

            if self.programs[i].is_empty() {
                log::warn!(
                    "Programs {} / {} is empty current idx: {}",
                    i,
                    self.programs.len(),
                    self.idx
                );
            }

            had_none |= self.programs[i].is_empty();
        }

        if had_pending {
            // roll back the current
            self.current = current;
            return MaybeResult::Pending;
        }

        if had_none {
            self.all_done = true;
            log::warn!("one of the programs was empty!");
            return MaybeResult::None;
        }

        self.idx += 1;

        if carry {
            self.all_done = true;
        }

        let prog = current
            .iter()
            .enumerate()
            .fold(Program::new(), |prog, (i, e)| {
                prog.merge(&self.programs[i][*e].clone())
            });

        MaybeResult::Some(prog)
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Program Builder for the ProgramsIter
////////////////////////////////////////////////////////////////////////////////////////////////////

impl ProgramBuilder for ProgramsIter {
    fn next(&mut self, _z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        match self.next_program() {
            Some(p) => MaybeResult::Some(p),
            None => MaybeResult::None,
        }
    }
}






