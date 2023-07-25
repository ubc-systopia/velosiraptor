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

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use smt2::Term;

use velosiast::ast::{VelosiAstBinOpExpr, VelosiAstExpr, VelosiAstMethod, VelosiAstUnitSegment};

use crate::programs::Program;

use crate::z3::{Z3TaskPriority, Z3WorkerPool};

use super::queries::{
    utils, BoolExprQueryBuilder, CompoundBoolExprQueryBuilder, MaybeResult, ProgramBuilder,
    ProgramVerifier, TranslateQueryBuilder,
};
use super::SynchronousSync;

/// represents the queries for the map operation
pub struct MapPrograms {
    /// iterator of the candidate programs
    candidate_programs: Box<dyn ProgramBuilder>,
    /// reference to the map function
    m_fn: Rc<VelosiAstMethod>,
    /// the starting program for the memory model
    starting_prog: Option<Rc<Program>>,
}

impl MapPrograms {
    pub fn new(
        unit: &VelosiAstUnitSegment,
        batch_size: usize,
        starting_prog: Option<Rc<Program>>,
    ) -> Self {
        log::info!(target : "[synth::map]", "setting up map synthesis.");

        let mut partial_programs = Vec::new();

        // obtain the op_fn, this is the map() function
        let m_op = unit
            .get_method("map")
            .unwrap_or_else(|| panic!("no method 'map' in unit {}", unit.ident()));

        // handle the translate function
        if let Some(m) = unit.get_method("translate") {
            // obtain the translate query
            let query = TranslateQueryBuilder::new(unit, m_op.clone(), m.clone())
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
            utils::add_method_preconds(unit, m_op, m, batch_size, false, &mut partial_programs);
        }

        // add the methods that must be true
        utils::add_methods_tagged_with_remap(unit, m_op, batch_size, false, &mut partial_programs);

        // we now have all the partial programs ready
        let query = if let Some(starting_prog) = &starting_prog {
            // here we have a starting program, that should have satisfied all the preconditions.
            // we now need to check if the program can be made to work with the memory model as well
            if let Some(p) = partial_programs.pop() {
                let goal_expr = partial_programs.into_iter().fold(p.goal_expr(), |acc, x| {
                    Rc::new(VelosiAstExpr::BinOp(VelosiAstBinOpExpr::land(
                        acc,
                        x.goal_expr(),
                    )))
                });

                // we got the goal expression that is now an AND of everything, so we can now
                // form the boolean expression

                BoolExprQueryBuilder::new(unit, m_op.clone(), goal_expr)
                    .mem_model(starting_prog.clone())
                    .build()
                    .map(|e| e.into())
            } else {
                None
            }
        } else {
            // construct a new compound query builder
            CompoundBoolExprQueryBuilder::new(unit, m_op.clone())
                .partial_programs(partial_programs, false)
                // .assms()
                .all()
                .map(|e| e.into())
        };

        if let Some(query) = query {
            let query = ProgramVerifier::with_batchsize(
                unit.ident().clone(),
                query,
                batch_size,
                Z3TaskPriority::High,
            );

            Self {
                candidate_programs: query.into(),
                m_fn: m_op.clone(),
                // goal_exprs: Vec::new(),
                starting_prog,
            }
        } else {
            todo!("handle the case where there was no query here")
        }
    }
}

/// Implement the PrograBuilder trait for MapPrograms
impl ProgramBuilder for MapPrograms {
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
        writeln!(f, "{i} @ MapPrograms",)?;
        self.candidate_programs.do_fmt(f, indent + 4, debug)
    }
}

/// Implement `SynchronousSync` for `UnmapPrograms`
impl SynchronousSync for MapPrograms {}

/// Implement `From` for `MapPrograms`
///
/// To allow conversions from MapPrograms -> Box<dyn ProgramBuilder>
impl From<MapPrograms> for Box<dyn ProgramBuilder> {
    fn from(q: MapPrograms) -> Self {
        Box::new(q)
    }
}

/// Implement the Display trait for MapPrograms
impl Display for MapPrograms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, false)
    }
}

/// Implement the Debug trait for MapPrograms
impl Debug for MapPrograms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, true)
    }
}
