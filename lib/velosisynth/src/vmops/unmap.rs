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

use velosiast::ast::{
    VelosiAstExpr, VelosiAstMethod, VelosiAstMethodProperty, VelosiAstUnitSegment,
};

use crate::programs::Program;

use crate::z3::{Z3TaskPriority, Z3WorkerPool};

use super::queries::{
    BoolExprQueryBuilder, CompoundBoolExprQueryBuilder, MaybeResult, ProgramBuilder,
    ProgramVerifier,
};
use super::SynchronousSync;

pub struct UnmapPrograms {
    /// iterator of the candidate programs
    candidate_programs: Box<dyn ProgramBuilder>,
    /// reference to the map function
    m_fn: Rc<VelosiAstMethod>,
    /// vector of all expressions that need to be satisfied
    goal_exprs: Vec<Rc<VelosiAstExpr>>,
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

        // obtain the op_fn, this is the map() function
        let m_op = unit
            .get_method("unmap")
            .unwrap_or_else(|| panic!("no method 'map' in unit {}", unit.ident()));

        if let Some(_staring_prog) = &starting_prog {
            // here we have a starting program, that should have satisfied all the preconditions.
            // we now need to check if the program can be made to work with the memory model as well
        } else {
        }

        let mut partial_programs = Vec::new();

        // check if we have a valid function here,
        if let Some(v_fn) = unit.get_method("valid") {
            if let Some(body) = &v_fn.body {
                if !body.is_const_expr() {
                    // the body is not a const expression so we can add this to the list of
                    // partial programs
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

        // now we've got all the partial programs and we can start verifying
        let query = CompoundBoolExprQueryBuilder::new(unit, m_op.clone())
            .partial_programs(partial_programs, false)
            .order_preserving() // set it to be order preserving
            // .assms()
            .any();

        let candidate_programs = ProgramVerifier::with_batchsize(
            unit.ident().clone(),
            query.into(),
            batch_size,
            Z3TaskPriority::High,
        )
        .into();

        UnmapPrograms {
            candidate_programs,
            m_fn: m_op.clone(),
            goal_exprs: Vec::new(),
            starting_prog,
        }
    }
}

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

impl SynchronousSync for UnmapPrograms {}

/// Implement `From` for `ProgramVerifier
///
/// To allow conversions from ProgramVerifier -> Box<dyn ProgramBuilder>
impl From<UnmapPrograms> for Box<dyn ProgramBuilder> {
    fn from(q: UnmapPrograms) -> Self {
        Box::new(q)
    }
}

impl Display for UnmapPrograms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, false)
    }
}

impl Debug for UnmapPrograms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, true)
    }
}

/// this functions collects the methods tagged with `remap` and adds them to the partial programs
fn add_methods_tagged_with_remap(
    unit: &VelosiAstUnitSegment,
    m_op: &Rc<VelosiAstMethod>,
    batch_size: usize,
    partial_programs: &mut Vec<Box<dyn ProgramBuilder>>,
) {
    for r_fn in unit.methods.values() {
        // if the property is not set to remap, we don't care about it
        if !r_fn.properties.contains(&VelosiAstMethodProperty::Remap)
            || r_fn.ident().as_str() == "valid"
        {
            log::debug!(
                target : "[synth::map]",
                "skipping method {} (not remap, or was valid)", r_fn.ident()
            );
            continue;
        }

        // we don't care about abstract or synth methods, the return type should always be boolean
        if r_fn.is_abstract || r_fn.is_synth || !r_fn.rtype.is_boolean() {
            log::debug!(
                target : "[synth::map]",
                "skipping method {} (abstract, synth, or not boolean)", r_fn.ident()
            );
            continue;
        }

        // split the body expressions into a list of conjuncts forming a CNF
        let exprs = r_fn
            .body
            .as_ref()
            .map(|body| body.split_cnf())
            .unwrap_or_else(|| panic!("no body for method {}", r_fn.ident()));

        log::info!(
            target : "[synth::map]",
            "handling method {}", r_fn.ident()
        );

        // build the query for the expressions of the body of the function,
        let query: Option<Box<dyn ProgramBuilder>> = match exprs.as_slice() {
            [] => unreachable!("slice of expressions was empty?"),
            [exp] => {
                log::debug!(target : "[synth::map]","single expr body {}", exp);

                // just a single expression here
                BoolExprQueryBuilder::new(unit, m_op.clone(), exp.clone())
                    // .assms(): No assumptions, as they will be added by the map.assms()
                    .variable_references(false)
                    .negate(true) // we negate the expression here
                    .build()
                    .map(|e| e.into())
            }
            _ => {
                log::debug!(target : "[synth::map]", "mutliple expr body");

                // handle all the expressions
                CompoundBoolExprQueryBuilder::new(unit, m_op.clone())
                    .exprs(exprs)
                    // .assms(): No assumptions, as they will be added by the map.assms()
                    .negate() // !(A && B && C), we convert this to !A || !B || !C
                    .all()
                    .map(|e| e.into())
            }
        };

        // add the program verifier and add the query to the list
        if let Some(query) = query {
            log::debug!(target : "[synth::map]", "adding query to partial programs");
            partial_programs.push(
                ProgramVerifier::with_batchsize(
                    unit.ident().clone(),
                    query,
                    batch_size,
                    Z3TaskPriority::Medium,
                )
                .into(),
            );
        }
    }
}
