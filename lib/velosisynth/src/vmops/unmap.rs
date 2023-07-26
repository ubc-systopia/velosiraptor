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

//! Synthesis of Virtual Memory Operations: Unmap

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use smt2::Term;

use velosiast::ast::{VelosiAstBinOpExpr, VelosiAstExpr, VelosiAstMethod, VelosiAstUnitSegment};

use crate::programs::Program;

use crate::z3::{Z3TaskPriority, Z3WorkerPool};

use super::queries::{
    utils, BoolExprQueryBuilder, CompoundBoolExprQueryBuilder, MaybeResult, ProgramBuilder,
    ProgramVerifier,
};
use super::SynchronousSync;

pub struct UnmapPrograms {
    /// iterator of the candidate programs
    candidate_programs: Box<dyn ProgramBuilder>,
    /// reference to the map function
    m_fn: Rc<VelosiAstMethod>,
    /// the starting program for the memory model
    starting_prog: Option<Rc<Program>>,
}

impl UnmapPrograms {
    pub fn new(
        unit: &VelosiAstUnitSegment,
        batch_size: usize,
        starting_prog: Option<Rc<Program>>,
    ) -> Self {
        log::info!(target : "[synth::unmap]", "setting up unmap synthesis.");

        let mut partial_programs = Vec::new();

        // obtain the op_fn, this is the map() function
        let m_op = unit
            .get_method("unmap")
            .unwrap_or_else(|| panic!("no method 'map' in unit {}", unit.ident()));

        // check if we have a valid function here, easiest if we can just invert that
        if let Some(v_fn) = unit.get_method("valid") {
            if let Some(body) = &v_fn.body {
                if !body.is_const_expr() {
                    // the body is not a const expression so we can add this to the list of
                    // partial programs, if it were a const expression then it's either always
                    // true or always false, so we don't need to add it to the list of partial
                    let query = BoolExprQueryBuilder::new(unit, m_op.clone(), body.clone())
                        // .assms(): No assumptions, as they will be added by the map.assms()
                        .variable_references(false)
                        .negate(true) // we negate the expression here
                        .build()
                        .map(|e| e.into());
                    if let Some(query) = query {
                        partial_programs.push(query);
                    }
                }
            }
        }

        // next we add the methods
        utils::add_methods_tagged_with_remap(unit, m_op, batch_size, true, None, &mut partial_programs);

        // if none of them can be invalidated we see whether there are pre-conditions in the
        // translate function that we may select from
        if let Some(m) = unit.get_method("translate") {
            utils::add_method_preconds(unit, m_op, m, batch_size, true, None,&mut partial_programs);
        }

        let query = if let Some(starting_prog) = &starting_prog {
            // here we have a starting program, that should have satisfied all the preconditions.
            // we now need to check if the program can be made to work with the memory model as well
            if let Some(p) = partial_programs.pop() {
                let goal_expr = partial_programs.into_iter().fold(p.goal_expr(), |acc, x| {
                    Rc::new(VelosiAstExpr::BinOp(VelosiAstBinOpExpr::lor(
                        acc,
                        x.goal_expr(),
                    )))
                });

                // we got the goal expression that is now an AND of everything, so we can now
                // form the boolean expression

                BoolExprQueryBuilder::new(unit, m_op.clone(), goal_expr)
                    .mem_model(starting_prog.clone())
                    .build()
                    .expect("no query?")
                    .into()
            } else {
                unreachable!("there were no partial programs?")
            }
        } else {
            // now we've got all the partial programs and we can start verifying
            CompoundBoolExprQueryBuilder::new(unit, m_op.clone())
                .partial_programs(partial_programs, false)
                .order_preserving() // set it to be order preserving
                // .assms()
                .any()
                .into()
        };

        let candidate_programs = ProgramVerifier::with_batchsize(
            unit.ident().clone(),
            query,
            batch_size,
            Z3TaskPriority::High,
        )
        .into();

        UnmapPrograms {
            candidate_programs,
            m_fn: m_op.clone(),
            // goal_exprs: Vec::new(),
            starting_prog,
        }
    }
}

/// Implement the PrograBuilder trait for UnmapPrograms
impl ProgramBuilder for UnmapPrograms {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        self.candidate_programs.next(z3)
    }

    fn m_op(&self) -> &VelosiAstMethod {
        self.m_fn.as_ref()
    }

    /// the assumptions for the program
    fn assms(&self) -> Rc<Vec<Term>> {
        unimplemented!()
    }

    /// the expression that the program needs to establish
    fn goal_expr(&self) -> Rc<VelosiAstExpr> {
        unimplemented!()
    }

    fn do_fmt(&self, f: &mut Formatter<'_>, indent: usize, debug: bool) -> FmtResult {
        let i = " ".repeat(indent);
        writeln!(f, "{i} @ UnmapPrograms",)?;
        self.candidate_programs.do_fmt(f, indent + 4, debug)
    }
}

/// Implement `SynchronousSync` for `UnmapPrograms`
impl SynchronousSync for UnmapPrograms {}

/// Implement `From` for `ProgramVerifier
///
/// To allow conversions from UnmapPrograms -> Box<dyn ProgramBuilder>
impl From<UnmapPrograms> for Box<dyn ProgramBuilder> {
    fn from(q: UnmapPrograms) -> Self {
        Box::new(q)
    }
}

/// Implement the Display trait for UnmapPrograms
impl Display for UnmapPrograms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, false)
    }
}

/// Implement the Debug trait for UnmapPrograms
impl Debug for UnmapPrograms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, true)
    }
}
