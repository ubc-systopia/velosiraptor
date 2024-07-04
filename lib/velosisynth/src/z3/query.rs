// Velosiraptor Synthesizer
//
//
// MIT License
//
// Copyright (c) 2021 Systopia Lab, Computer Science, University of British Columbia
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

// standard library imports
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use std::time::Instant;

// external library imports
use smt2::Smt2Context;

// own crate imports
use crate::{model, Program};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3Tickets: a identifies the Z3 query
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents a Z3 Query identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Z3Ticket(pub usize);

// implementation of [Display] for [Z3Ticket]]
impl Display for Z3Ticket {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.0)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Timestamps
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Z3TimeStamp {
    /// time of the creation of the Z3Query
    Create,
    /// the query has been submitted to the worker pool
    Submit,
    /// a worker dispatched the query
    Dispatch,
    /// smtlib2 formatting completed
    FmtSmt,
    /// command sent to the solver
    SendCmd,
    /// solver execution completed
    SolverDone,
    ///
    Done,
}

// implementation of [Display] for [Z3TimeStamp]]
impl Display for Z3TimeStamp {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use Z3TimeStamp::*;
        match self {
            Create => {
                write!(f, "foo")
            }
            Submit => {
                write!(f, "foo")
            }
            Dispatch => {
                write!(f, "foo")
            }
            FmtSmt => {
                write!(f, "foo")
            }
            SendCmd => {
                write!(f, "foo")
            }
            SolverDone => {
                write!(f, "foo")
            }
            Done => {
                write!(f, "foo")
            }
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3Query
////////////////////////////////////////////////////////////////////////////////////////////////////

/// represents a Z3 smt query
#[derive(Clone)]
pub struct Z3Query {
    /// the operations of this query for bookkeeping purposes
    prog: Option<Arc<Program>>,
    /// the goal of the program
    goal: Option<Arc<String>>,
    /// the statements to be executed
    smt: Vec<Arc<Smt2Context>>,
    /// time durations for tracing
    timestamps: Vec<(Z3TimeStamp, Instant)>,
    ///
    is_complex: bool,
}

impl Z3Query {
    /// creates a new Z3 Query with a empty context
    pub fn new() -> Self {
        Self::with_context(Smt2Context::new())
    }

    /// Creates a new Z3 Query with the given SMT context
    pub fn with_context(smt: Smt2Context) -> Self {
        let mut timestamps = Vec::with_capacity(10);
        timestamps.push((Z3TimeStamp::Create, Instant::now()));
        Self {
            prog: None,
            goal: None,
            smt: vec![Arc::new(smt)],
            timestamps,
            is_complex: false,
        }
    }

    /// Creates a new Z3 Query with multiple SMT contexts and adds the model prelude
    pub fn with_model_contexts(mut smt: Vec<Arc<Smt2Context>>) -> Self {
        smt.insert(0, Arc::new(model::prelude()));

        Self {
            prog: None,
            goal: None,
            smt,
            timestamps: Vec::with_capacity(10),
            is_complex: false,
        }
    }

    pub fn clone_without_program(&self) -> Self {
        let mut timestamps = Vec::with_capacity(10);
        timestamps.push((Z3TimeStamp::Create, Instant::now()));
        Self {
            prog: None,
            goal: None,
            smt: self.smt.clone(),
            timestamps,
            is_complex: false,
        }
    }

    pub fn clone_without_timestamps(&self) -> Self {
        let mut timestamps = Vec::with_capacity(10);
        timestamps.push((Z3TimeStamp::Create, Instant::now()));
        Self {
            prog: self.prog.clone(),
            goal: self.goal.clone(),
            smt: self.smt.clone(),
            timestamps,
            is_complex: false,
        }
    }

    /// creates a new Z3 Query to reset the solver
    pub fn reset() -> Self {
        // construct the context and add the reset condition
        let mut smt = Smt2Context::new();
        smt.reset();

        Self::with_context(smt)
    }

    /// sets the operations field of the query (book keeping purpose)
    pub fn set_program(&mut self, p: Program) -> &mut Self {
        self.prog = Some(Arc::new(p));
        self
    }

    pub fn set_goal(&mut self, goal: String) -> &mut Self {
        self.goal = Some(Arc::new(goal));
        self
    }

    /// sets the SMT context of the query
    pub fn set_smt(&mut self, smt: Smt2Context) -> &mut Self {
        self.smt = vec![Arc::new(smt)];
        self
    }

    pub fn set_complex(&mut self) -> &mut Self {
        self.is_complex = true;
        self
    }

    pub fn is_complex(&self) -> bool {
        self.is_complex
    }

    /// obtains a reference to this context
    pub fn smt_contexts(&self) -> &[Arc<Smt2Context>] {
        &self.smt
    }

    /// obtains a reference to the operations of this query
    pub fn program(&self) -> Option<&Program> {
        self.prog.as_ref().map(|f| f.as_ref())
    }

    pub fn take_program(&mut self) -> Option<Program> {
        self.prog.take().map(|f| f.as_ref().to_owned())
    }

    /// records a timestamp for tracing
    pub fn timestamp(&mut self, id: Z3TimeStamp) -> Instant {
        let inst = Instant::now();
        self.timestamps.push((id, inst));
        inst
    }

    pub fn timestamps(&self) -> &[(Z3TimeStamp, Instant)] {
        &self.timestamps
    }

    /// checks whether the query is empty or not
    pub fn is_empty(&self) -> bool {
        self.smt.len() == 1 && self.smt[0].is_empty()
    }
}

impl Default for Z3Query {
    fn default() -> Self {
        Self::new()
    }
}

impl From<Smt2Context> for Z3Query {
    fn from(item: Smt2Context) -> Self {
        Z3Query::with_context(item)
    }
}

// impl From<Z3Query> for Smt2Context {
//     fn from(item: Z3Query) -> Self {
//         item.smt.
//     }
// }

impl Display for Z3Query {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "Query: {:?}",
            self.smt.iter().map(|s| s.to_string()).collect::<Vec<_>>()
        )
    }
}

impl Debug for Z3Query {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "Query: {:?}",
            self.smt.iter().map(|s| s.to_string()).collect::<Vec<_>>()
        )
    }
}

impl Eq for Z3Query {}

impl PartialEq for Z3Query {
    fn eq(&self, other: &Self) -> bool {
        match (&self.prog, &self.goal) {
            (Some(_), Some(_)) => self.prog == other.prog && self.goal == other.goal,
            _ => self.smt == other.smt,
        }
    }
}

impl Hash for Z3Query {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match (&self.prog, &self.goal) {
            (Some(p), Some(g)) => {
                p.hash(state);
                g.hash(state);
            }
            _ => self.smt.hash(state),
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3Query
////////////////////////////////////////////////////////////////////////////////////////////////////

/// represents a result obtained from executing a Z3 query
#[derive(Clone)]
pub struct Z3Result {
    /// returns the task again
    query: Option<Box<Z3Query>>,

    /// the result of the task
    result: String,
}

impl Z3Result {
    /// creates a new Z3 result without the query
    pub fn new(result: String) -> Self {
        Self {
            query: None,
            result,
        }
    }

    pub fn clone_with_query(&self, query: Box<Z3Query>) -> Self {
        Self {
            query: Some(query),
            result: self.result.clone(),
        }
    }

    /// creates a new Z3 result with the given query
    pub fn with_query(query: Box<Z3Query>, result: String) -> Self {
        Self {
            query: Some(query),
            result,
        }
    }

    // pub fn print_timestamps(&self) {
    //     if let Some(query) = &self.query {
    //         query.print_timestamps();
    //     }
    // }

    /// sets the query with the result
    pub fn set_query(&mut self, query: Box<Z3Query>) {
        self.query = Some(query);
    }

    /// whether the result has the associated query
    pub fn has_query(&self) -> bool {
        self.query.is_some()
    }

    /// returns the associated query
    pub fn query(&self) -> &Z3Query {
        self.query.as_ref().unwrap()
    }

    pub fn query_mut(&mut self) -> &mut Z3Query {
        self.query.as_mut().unwrap()
    }

    /// takes the query from the result
    pub fn take_query(&mut self) -> Option<Box<Z3Query>> {
        self.query.take()
    }

    /// whether the result has errors
    pub fn has_errors(&self) -> bool {
        self.result.lines().any(|f| f.starts_with("(error"))
    }

    pub fn collect_errors(&self) -> Vec<&str> {
        let mut res = Vec::new();
        for l in self.result.lines() {
            if l.starts_with("(error") {
                res.push(&l[7..]);
            }
        }
        res
    }

    /// returns the result of the task
    pub fn result(&self) -> &str {
        &self.result
    }
}

impl Display for Z3Result {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Result: {}", self.result)
    }
}

impl Debug for Z3Result {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Result: {}", self.result)
    }
}

impl From<Z3Result> for Box<Z3Query> {
    fn from(item: Z3Result) -> Self {
        item.query.unwrap()
    }
}

impl From<Z3Result> for Z3Query {
    fn from(item: Z3Result) -> Self {
        *item.query.unwrap()
    }
}
