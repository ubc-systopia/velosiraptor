// VelosiParser -- a parser for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2021, 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiParser -- The Velosiraptor Parser
//!
//! The VelosiParser consumes the lexed TokenStream and produces a parse tree for the
//! for further processing.

// used standard library functionality

use std::env;
use std::path::PathBuf;
use std::rc::Rc;

use std::fmt::{Display, Formatter, Result as FmtResult};

use smt2::Smt2Context;

// public re-exports

// crate modules
mod error;
mod model;
mod operation;
mod programs;
mod vmops;
mod z3;

use velosiast::ast::VelosiAstUnitSegment;

pub use error::{VelosiSynthError, VelosiSynthIssues};
pub use operation::{OpExpr, Operation};
pub use programs::{Program, ProgramsBuilder};
pub use z3::{Z3Query, Z3Ticket, Z3Worker, Z3WorkerPool};

#[macro_export]
macro_rules! synth_result_return (($res: expr, $issues: expr) => (
    if $issues.is_ok() {
        Result::Ok($res)
    } else {
        Result::Err($issues)
    }
));

#[macro_export]
macro_rules! synth_result_unwrap (($e: expr, $issues: expr) => (
    match $e {
        Result::Ok(t) => t,
        Result::Err(e) => {
            $issues.merge(e.into());
            return Result::Err($issues)
        },
    }
));

pub struct SynthResult {
    map: Program,
    unmap: Program,
    protect: Program,
}

impl Display for SynthResult {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "Programs:\n  map:\n    {}\n  unmap:\n    {}\n  protect:\n    {}",
            self.map, self.unmap, self.protect
        )
    }
}

pub struct SynthZ3 {
    ast: Rc<VelosiAstUnitSegment>,
    outdir: PathBuf,
    ncpu: usize,
    workerpool: Option<Z3WorkerPool>,
}

impl SynthZ3 {
    pub fn new(ast: Rc<VelosiAstUnitSegment>) -> Self {
        // get the outdir from the current path
        let outdir = env::current_dir().unwrap();
        let outdir = outdir.join("synth");

        Self::with_outdir(ast, outdir)
    }

    pub fn with_outdir(ast: Rc<VelosiAstUnitSegment>, outdir: PathBuf) -> Self {
        Self::with_ncpu(ast, outdir, 1)
    }

    pub fn with_ncpu(ast: Rc<VelosiAstUnitSegment>, outdir: PathBuf, ncpu: usize) -> Self {
        SynthZ3 {
            ast,
            outdir,
            ncpu,
            workerpool: None,
        }
    }

    pub fn set_parallelism(&mut self, ncpu: usize) {
        // make sure we don't have anything running anymore
        self.terminate();

        let workerpool = Z3WorkerPool::with_num_workers(ncpu, Some(&self.outdir));

        self.workerpool = Some(workerpool);
        self.ncpu = ncpu;
    }

    pub fn terminate(&mut self) {
        if let Some(mut workerpool) = self.workerpool.take() {
            workerpool.terminate();
        }
    }

    fn run_smt2(&mut self, ctx: Smt2Context) -> Result<(), VelosiSynthIssues> {
        if self.workerpool.is_none() {
            let workerpool = Z3WorkerPool::with_num_workers(self.ncpu, Some(&self.outdir));
            self.workerpool = Some(workerpool);
        }

        let workerpool = self.workerpool.as_mut().unwrap();
        workerpool.reset_with_context(Z3Query::from(ctx));
        Ok(())
    }

    pub fn create_model(&mut self) -> Result<(), VelosiSynthIssues> {
        self.run_smt2(model::create(&self.ast))
    }

    pub fn sanity_check(&mut self) -> Result<(), VelosiSynthIssues> {
        log::info!(target: "[SynthZ3]", "running sanity checks on the model.");
        let mut issues = VelosiSynthIssues::new();

        issues.merge_result(vmops::sanity::check_precondition_satisfiability(
            &mut self.workerpool.as_mut().unwrap(),
            &self.ast,
            "map",
        ));
        issues.merge_result(vmops::sanity::check_precondition_satisfiability(
            &mut self.workerpool.as_mut().unwrap(),
            &self.ast,
            "unmap",
        ));
        issues.merge_result(vmops::sanity::check_precondition_satisfiability(
            &mut self.workerpool.as_mut().unwrap(),
            &self.ast,
            "protect",
        ));

        synth_result_return!((), issues)
    }

    pub fn synthesize_all(&mut self) -> Result<SynthResult, VelosiSynthIssues> {
        // have this more conditional
        self.create_model()?;

        let z3 = &mut self.workerpool.as_mut().unwrap();

        // --------------------------------------------------------------------------------------
        // Submit queries for all of the three vmops
        // --------------------------------------------------------------------------------------

        let map_queries = vmops::map::submit_fragment_queries(z3, &self.ast)?;
        let unmap_tickets = vmops::unmap::submit_queries(z3, &self.ast)?;
        let protect_tickets = vmops::protect::submit_queries(z3, &self.ast)?;

        // --------------------------------------------------------------------------------------
        // Process the results
        // --------------------------------------------------------------------------------------

        let map_queries = vmops::map::process_fragment_queries(z3, &self.ast, map_queries)?;
        let unmap_results = vmops::unmap::check_queries(z3, unmap_tickets)?;
        let protect_results = vmops::protect::check_queries(z3, protect_tickets)?;

        // --------------------------------------------------------------------------------------
        // Construct candiate programs
        // --------------------------------------------------------------------------------------

        let map_queries = vmops::map::process_block_queries(z3, &self.ast, map_queries)?;
        let unmap_programs = vmops::unmap::construct_programs(z3, unmap_results)?;
        let protect_programs = vmops::protect::construct_programs(z3, protect_results)?;

        // --------------------------------------------------------------------------------------
        // Construct candiate programs
        // --------------------------------------------------------------------------------------

        let map_program = vmops::map::process_program_queries(z3, map_queries)?;
        let unmap = vmops::unmap::check_programs(z3, unmap_programs)?;
        let protect = vmops::protect::check_programs(z3, protect_programs)?;

        Ok(SynthResult {
            map: map_program,
            unmap,
            protect,
        })
    }

    pub fn synthesize_map(&mut self) -> Result<Program, VelosiSynthIssues> {
        // have this more conditional
        self.create_model()?;

        vmops::map::synthesize(&mut self.workerpool.as_mut().unwrap(), &self.ast)
    }

    pub fn synthesize_unmap(&mut self) -> Result<Program, VelosiSynthIssues> {
        // have this more conditional
        self.create_model()?;
        vmops::unmap::synthesize(&mut self.workerpool.as_mut().unwrap(), &self.ast)
    }

    pub fn synthesize_protect(&mut self) -> Result<Program, VelosiSynthIssues> {
        // have this more conditional
        self.create_model()?;
        vmops::protect::synthesize(&mut self.workerpool.as_mut().unwrap(), &self.ast)
    }
}
