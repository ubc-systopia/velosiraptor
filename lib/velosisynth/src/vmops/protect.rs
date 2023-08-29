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
use crate::ProgramsIter;

use crate::z3::{Z3TaskPriority, Z3WorkerPool};

use super::queries::{
    utils, BoolExprQueryBuilder, CompoundBoolExprQueryBuilder, MaybeResult, ProgramBuilder,
    ProgramVerifier, TranslateQueryBuilder,
};
use super::SynchronousSync;

pub struct ProtectPrograms {
    /// iterator of the candidate programs
    candidate_programs: Box<dyn ProgramBuilder>,
}

impl ProtectPrograms {
    pub fn new(
        unit: &VelosiAstUnitSegment,
        batch_size: usize,
        _starting_prog: Option<Rc<Program>>,
    ) -> Self {
        log::info!(target : "[synth::protect]", "setting up protect synthesis.");

        let mut partial_programs = Vec::new();

        // obtain the op_fn, this is the map() function
        let m_op = unit
            .get_method("protect")
            .unwrap_or_else(|| panic!("no method 'map' in unit {}", unit.ident()));

        // handle the translate function
        if let Some(m) = unit.get_method("translate") {
            // obtain the translate query
            let query = TranslateQueryBuilder::new(unit, m_op.clone(), m.clone())
                .no_change()
                .build()
                .expect("no query?");

            partial_programs.push(
                ProgramVerifier::with_batchsize(
                    unit.ident().clone(),
                    query.into(),
                    batch_size,
                    Z3TaskPriority::Low,
                )
                .into(),
            );

            // add the pre-conditions for the translate
            utils::add_method_preconds(
                unit,
                m_op,
                m,
                batch_size,
                false,
                Some(true),
                &mut partial_programs,
            );
        }

        // add the methods that must be true
        utils::add_methods_tagged_with_remap(
            unit,
            m_op,
            batch_size,
            false,
            Some(true),
            &mut partial_programs,
        );

        let query = if let Some(staring_prog) = &starting_prog {
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
                    .mem_model(staring_prog.clone())
                    .build()
                    .expect("no query?")
                    .into()
            } else {
                // there were no starting programs?
                ProgramsIter::default().into()
            }
        } else {
            CompoundBoolExprQueryBuilder::new(unit, m_op.clone())
                .partial_programs(partial_programs, false)
                // .assms()
                .all()
                .expect("query?")
                .into()
        };

        let query = ProgramVerifier::with_batchsize(
            unit.ident().clone(),
            query,
            batch_size,
            Z3TaskPriority::High,
        );

        Self {
            candidate_programs: Box::new(query),
        }
    }
}

impl ProgramBuilder for ProtectPrograms {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        self.candidate_programs.next(z3)
    }

    fn m_op(&self) -> &VelosiAstMethod {
        unimplemented!()
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
        writeln!(f, "{i} @ ProtectPrograms",)?;
        self.candidate_programs.do_fmt(f, indent + 4, debug)
    }
}

impl SynchronousSync for ProtectPrograms {}

/// Implement `From` for `ProgramVerifier
///
/// To allow conversions from ProgramVerifier -> Box<dyn ProgramBuilder>
impl From<ProtectPrograms> for Box<dyn ProgramBuilder> {
    fn from(q: ProtectPrograms) -> Self {
        Box::new(q)
    }
}

impl Display for ProtectPrograms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, false)
    }
}

impl Debug for ProtectPrograms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, true)
    }
}
