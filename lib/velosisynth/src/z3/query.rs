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
use crate::Program;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3Tickets: a identifies the Z3 query
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents a Z3 Query identifier
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Z3Ticket(pub usize);

// implementation of [Display] for [Z3Ticket]]
impl Display for Z3Ticket {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.0)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Z3Query
////////////////////////////////////////////////////////////////////////////////////////////////////

/// represents a Z3 smt query
pub struct Z3Query {
    /// the operations of this query for bookkeeping purposes
    prog: Option<Program>,

    /// the goal of the program
    goal: Option<String>,

    /// the statements to be executed
    smt: Arc<Smt2Context>,

    /// the timestamps fo tracing
    timestamps: Vec<(&'static str, Instant)>,
}

impl Z3Query {
    /// creates a new Z3 Query with a empty context
    pub fn new() -> Self {
        Self::with_context(Smt2Context::new())
    }

    /// Creates a new Z3 Query with the given SMT context
    pub fn with_context(smt: Smt2Context) -> Self {
        Self {
            prog: None,
            goal: None,
            smt: Arc::new(smt),
            timestamps: Vec::with_capacity(10),
        }
    }

    pub fn clone_without_program(&self) -> Self {
        Self {
            prog: None,
            goal: None,
            smt: self.smt.clone(),
            timestamps: Vec::with_capacity(0),
        }
    }

    pub fn clone_without_timestamps(&self) -> Self {
        Self {
            prog: self.prog.clone(),
            goal: self.goal.clone(),
            smt: self.smt.clone(),
            timestamps: Vec::with_capacity(0),
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
        self.prog = Some(p);
        self
    }

    pub fn set_goal(&mut self, goal: String) -> &mut Self {
        self.goal = Some(goal);
        self
    }

    /// sets the SMT context of the query
    pub fn set_smt(&mut self, smt: Smt2Context) -> &mut Self {
        self.smt = Arc::new(smt);
        self
    }

    /// obtains a reference to this context
    pub fn smt_context(&self) -> &Smt2Context {
        &self.smt
    }

    /// obtains a reference to the operations of this query
    pub fn program(&self) -> Option<&Program> {
        self.prog.as_ref()
    }

    pub fn take_program(&mut self) -> Option<Program> {
        self.prog.take()
    }

    pub fn program_mut(&mut self) -> &mut Program {
        self.prog.as_mut().unwrap()
    }

    /// records a timestamp for tracing
    pub fn timestamp(&mut self, name: &'static str) {
        self.timestamps.push((name, Instant::now()));
    }

    /// prints the timestamp values
    pub fn print_timestamps(&self) {
        if self.timestamps.is_empty() {
            println!("stats: no timestamps");
            return;
        }

        let (_, t_start) = self.timestamps[0];
        let mut t_last = t_start;
        for (i, (name, now)) in self.timestamps.iter().enumerate() {
            let diff = now.saturating_duration_since(t_last);
            t_last = *now;
            if i == 0 {
                continue;
            }
            print!("{}, {:7}, us,  ", name, diff.as_micros());
        }
        let diff = t_last.saturating_duration_since(t_start);
        println!("elapsed, {:7}, us  ", diff.as_micros());
    }

    /// checks whether the query is empty or not
    pub fn is_empty(&self) -> bool {
        self.smt.is_empty()
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
        write!(f, "Query: {}", self.smt)
    }
}

impl Debug for Z3Query {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Query: {}", self.smt)
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
pub struct Z3Result {
    /// returns the task again
    query: Option<Z3Query>,

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

    pub fn clone_with_query(&self, query: Z3Query) -> Self {
        Self {
            query: Some(query),
            result: self.result.clone(),
        }
    }

    /// creates a new Z3 result with the given query
    pub fn with_query(query: Z3Query, result: String) -> Self {
        Self {
            query: Some(query),
            result,
        }
    }

    pub fn print_timestamps(&self) {
        if let Some(query) = &self.query {
            query.print_timestamps();
        }
    }

    /// sets the query with the result
    pub fn set_query(&mut self, query: Z3Query) {
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
    pub fn take_query(&mut self) -> Option<Z3Query> {
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

impl From<Z3Result> for Z3Query {
    fn from(item: Z3Result) -> Self {
        item.query.unwrap()
    }
}
