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
use std::fmt;

// external library imports
use smt2::{Smt2Command, Smt2Context};

// own crate imports
use super::operations::Program;

/// represents a query ticket / identifier
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Z3Ticket(pub usize);

impl fmt::Display for Z3Ticket {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// represents a Z3 smt query
pub struct Z3Query {
    /// the operations of this query for bookkeeping purposes
    prog: Option<Program>,

    /// the statements to be executed
    smt: Smt2Context,
}

impl Z3Query {
    /// creates a new Z3 Query
    pub fn new() -> Self {
        Self::with_context(Smt2Context::new())
    }

    /// Creates a new Z3 Query with the given SMT context
    pub fn with_context(smt: Smt2Context) -> Self {
        Self { prog: None, smt }
    }

    /// whether the query is emtpy
    pub fn is_empty(&self) -> bool {
        self.smt.is_empty()
    }

    /// creates a new Z3 reset query
    pub fn reset() -> Self {
        // construct the context and add the reset condition
        let mut smt = Smt2Context::new();
        smt.reset();

        Z3Query { prog: None, smt }
    }

    /// sets the operations field of the query (book keeping purpose)
    pub fn set_program(&mut self, p: Program) -> &mut Self {
        self.prog = Some(p);
        self
    }

    /// sets the SMT context of the query
    pub fn set_smt(&mut self, smt: Smt2Context) -> &mut Self {
        self.smt = smt;
        self
    }

    /// adds a command to the SMT context
    pub fn add_command(&mut self, cmd: Smt2Command) -> &mut Self {
        self.smt.add_command(cmd);
        self
    }

    /// obtains a reference to this context
    pub fn smt_context(&self) -> &Smt2Context {
        &self.smt
    }

    /// obtains a mutable reference to the smt context of this query
    pub fn smt_context_mut(&mut self) -> &mut Smt2Context {
        &mut self.smt
    }

    /// obtains a reference to the operations of this query
    pub fn program(&self) -> Option<&Program> {
        self.prog.as_ref()
    }

    pub fn program_mut(&mut self) -> &mut Program {
        self.prog.as_mut().unwrap()
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

impl From<Z3Query> for Smt2Context {
    fn from(item: Z3Query) -> Self {
        item.smt
    }
}

impl fmt::Display for Z3Query {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Query: {}", self.smt)
    }
}

impl fmt::Debug for Z3Query {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Query: {}", self.smt)
    }
}

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

    /// creates a new Z3 result with the given query
    pub fn with_query(query: Z3Query, result: String) -> Self {
        Self {
            query: Some(query),
            result,
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

    /// returns the result of the task
    pub fn result(&self) -> &str {
        &self.result
    }
}

impl fmt::Display for Z3Result {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Result: {}", self.result)
    }
}

impl fmt::Debug for Z3Result {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Result: {}", self.result)
    }
}

// fn op_expr_get_variables(counter: &mut u64, op: &mut OpExpr) -> Vec<String> {
//     match op {
//         OpExpr::Num(_) => {
//             let var = format!("x!{}", counter);
//             *counter += 1;
//             *op = OpExpr::Var(var.clone());
//             vec![var]
//         }
//         OpExpr::Var(_) => Vec::new(),
//         OpExpr::Shl(a, b) => {
//             let mut a_vars = op_expr_get_variables(counter, a);
//             let b_vars = op_expr_get_variables(counter, b);
//             a_vars.extend(b_vars);
//             a_vars
//         }
//         OpExpr::Shr(a, b) => {
//             let mut a_vars = op_expr_get_variables(counter, a);
//             let b_vars = op_expr_get_variables(counter, b);
//             a_vars.extend(b_vars);
//             a_vars
//         }
//         _ => panic!("unimplemented"),
//     }
// }

// fn ops_get_variables(ops: &mut Vec<Operation>) -> Vec<String> {
//     let mut vars = Vec::new();
//     let mut counter = 0;
//     for op in ops.iter_mut() {
//         if let Operation::Insert { arg, .. } = op {
//             let new_vars = op_expr_get_variables(&mut counter, arg);
//             vars.extend(new_vars);
//         }
//     }
//     vars
// }

// fn ops_to_smt2(ops: &[Operation]) -> Smt2Context {
//     let mut smt = Smt2Context::new();
//     // for op in ops {
//     //     smt.add_command(op.to_smt2());
//     // }
//     // smt

//     smt
// }

// impl Z3Query {

//     pub fn to_smt2_string(&self) -> String {
//         match self {
//             Z3Query::MapOps(desc) => {
//                 // get the context first
//                 let mut s = desc
//                     .smt
//                     .as_ref()
//                     .map(|smt| smt.to_string())
//                     .unwrap_or_default();

//                 s
//             }
//             Z3Query::UnmapPos(desc) => {
//                 // get the context first
//                 let mut s = desc
//                     .smt
//                     .as_ref()
//                     .map(|smt| smt.to_string())
//                     .unwrap_or_default();

//                 s
//             }
//             Z3Query::ProtectOps(desc) => {
//                 // get the context first
//                 let mut s = desc
//                     .smt
//                     .as_ref()
//                     .map(|smt| smt.to_string())
//                     .unwrap_or_default();
//                 s
//             }
//             Z3Query::Reset => "(reset)".to_string(),
//             Z3Query::RawWithResult(ctx) => ctx.to_string(),
//             Z3Query::RawNoResult(ctx) => ctx.to_string(),
//         }
//     }
// }
