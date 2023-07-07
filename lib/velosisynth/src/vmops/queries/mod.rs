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

//! Synthesis of Virtual Memory Operations

pub mod precond;
pub mod queryhelper;
pub mod resultparser;
pub mod semantics;
pub mod semprecond;
pub mod utils;

mod boolexpr;
mod cnf;
mod translate;
mod verifier;

// std imports
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// library imports
use smt2::Term;
use velosiast::ast::{VelosiAstExpr, VelosiAstMethod};

// crate imports
use crate::programs::Program;
use crate::z3::Z3WorkerPool;

// re-exports
pub use boolexpr::{BoolExprQuery, BoolExprQueryBuilder};
pub use cnf::CompoundBoolExprQueryBuilder;
pub use translate::{TranslateQuery, TranslateQueryBuilder};
pub use verifier::{ProgramVerifier, DEFAULT_BATCH_SIZE};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Tri-State Result
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents a tri-state result type
///
/// When submitting queries and running them their result may not be available yet. In this case,
/// we distinguish the following three states:
#[derive(Clone, PartialEq, Eq)]
pub enum MaybeResult<T> {
    /// we have a result
    Some(T),
    /// the result is not yet available
    Pending,
    /// There are no results here, no programs that are being built
    None,
}

impl<T> MaybeResult<T> {
    pub fn is_some(&self) -> bool {
        matches!(self, MaybeResult::Some(_))
    }
    pub fn is_pending(&self) -> bool {
        matches!(self, MaybeResult::Pending)
    }
    pub fn is_none(&self) -> bool {
        matches!(self, MaybeResult::None)
    }

    pub fn unwrap(self) -> T {
        match self {
            MaybeResult::Some(t) => t,
            _ => panic!("unwrap called on MaybeResult::None or MaybeResult::Pending"),
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Program Builder Trait
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Program Builder Trait
///
/// This trait is used to generate new programs that then are verified by Z3 solver.
///
/// Namely, if the assumptions (`assms`) hold, then the program should establish the
/// goal expression (`goal_expr`).
///
/// ```smt
///   Forall VARS :: Assumptions ==> GoalExpr(Prog(VARS))
/// ```
pub trait ProgramBuilder {
    /// returns the next query to be submitted, or None if all have been submitted
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program>;

    /// obtains the reference to the method that is being synthesized (map, protect, unmap)
    fn m_op(&self) -> &VelosiAstMethod;

    /// additional assumptions for the program
    ///
    /// The assumptions are the pre-conditions of the program
    fn assms(&self) -> Rc<Vec<Term>>;

    /// the expression that the program needs to establish.
    ///
    /// This is the goal of the synthesis and the expression that must always hold
    /// given the assumptions (`assm`).
    ///
    /// Note, we do require a single expression here and not a vector as we want to
    /// be able to express negations and disjunctions as well where applicable
    fn goal_expr(&self) -> Rc<VelosiAstExpr>;

    /// returns whether or not we use the mem model
    ///
    /// This influeces whether we need to adapt the generated model in Z3
    fn mem_model(&self) -> bool {
        false
    }

    /// formats the program builder object for debugging
    fn do_fmt(&self, f: &mut Formatter<'_>, indent: usize, debug: bool) -> FmtResult;
}

impl Display for dyn ProgramBuilder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, false)
    }
}

impl Debug for dyn ProgramBuilder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, true)
    }
}
