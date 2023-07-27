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
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use smt2::Term;
use velosiast::ast::{VelosiAstExpr, VelosiAstMethod};

use crate::{z3::Z3WorkerPool, Program};

//use super::queryhelper::{MaybeResult, ProgramBuilder, QueryBuilder};
use super::MaybeResult;

use super::ProgramBuilder;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Translate Query
////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct ProgramSimplifier {
    /// the programs that this query builder handles
    programs: Box<dyn ProgramBuilder>,
    ///
    unoptimized: Option<Program>,
    // assms: Rc<Vec<Term>>,
    // m_op: Rc<VelosiAstMethod>,
    // m_translate: Rc<VelosiAstMethod>,
    // goal: Rc<VelosiAstExpr>,
}

impl ProgramSimplifier {
    pub fn new(programs: Box<dyn ProgramBuilder>) -> Self {
        ProgramSimplifier {
            programs,
            unoptimized: None,
        }
    }
}

impl ProgramBuilder for ProgramSimplifier {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        match self.programs.next(z3) {
            MaybeResult::Some(prog) => {
                if self.unoptimized.is_none() {
                    self.unoptimized = Some(prog.clone());
                }
                MaybeResult::Some(prog.simplify())
            }
            MaybeResult::Pending => MaybeResult::Pending,
            MaybeResult::None => {
                if let Some(prog) = self.unoptimized.take() {
                    MaybeResult::Some(prog)
                } else {
                    MaybeResult::None
                }
            }
        }
    }

    fn m_op(&self) -> &VelosiAstMethod {
        self.programs.m_op()
    }

    /// the assumptions for the program
    fn assms(&self) -> Rc<Vec<Term>> {
        self.programs.assms()
    }

    /// the expression that the program needs to establish
    fn goal_expr(&self) -> Rc<VelosiAstExpr> {
        self.programs.goal_expr()
    }

    fn do_fmt(&self, f: &mut Formatter<'_>, indent: usize, debug: bool) -> FmtResult {
        let i = " ".repeat(indent);
        writeln!(f, "{i}  + ProgramSimplifier")?;
        self.programs.do_fmt(f, indent + 4, debug)
    }
}

/// Implement `From` for `ProgramVerifier
///
/// To allow conversions from ProgramVerifier -> Box<dyn ProgramBuilder>
impl From<ProgramSimplifier> for Box<dyn ProgramBuilder> {
    fn from(q: ProgramSimplifier) -> Self {
        Box::new(q)
    }
}

impl Display for ProgramSimplifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, false)
    }
}

impl Debug for ProgramSimplifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, true)
    }
}
