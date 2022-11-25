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
use std::sync::Arc;
use std::time::Instant;

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

use crate::vmops::{MaybeResult, ProgramBuilder};
pub use error::{VelosiSynthError, VelosiSynthIssues};
pub use operation::{OpExpr, Operation};
pub use programs::{Program, ProgramsBuilder, ProgramsIter};
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
            "Programs:\n- map:\n    {}\n-unmap:\n    {}\n-protect:\n    {}",
            self.map, self.unmap, self.protect
        )
    }
}

pub struct SynthZ3 {
    ast: Rc<VelosiAstUnitSegment>,
    outdir: Arc<PathBuf>,
    ncpu: usize,
    workerpool: Option<Z3WorkerPool>,
    model_created: bool,
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
            outdir: Arc::new(outdir),
            ncpu,
            workerpool: None,
            model_created: false,
        }
    }

    pub fn set_parallelism(&mut self, ncpu: usize) {
        // make sure we don't have anything running anymore
        self.terminate();

        let logpath = if cfg!(debug_assertions) {
            log::warn!(target: "Z3Synth", "Enabling query logging");
            Some(self.outdir.clone())
        } else {
            Some(self.outdir.clone())
        };
        let workerpool = Z3WorkerPool::with_num_workers(ncpu, logpath);

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
            let logpath = if cfg!(debug_assertions) {
                log::warn!(target: "Z3Synth", "Enabling query logging");
                Some(self.outdir.clone())
            } else {
                Some(self.outdir.clone())
            };
            let workerpool = Z3WorkerPool::with_num_workers(self.ncpu, logpath);
            self.workerpool = Some(workerpool);
        }

        let workerpool = self.workerpool.as_mut().unwrap();
        workerpool.reset_with_context(Z3Query::from(ctx));
        Ok(())
    }

    pub fn create_model(&mut self) -> Result<(), VelosiSynthIssues> {
        if !self.model_created {
            self.model_created = true;
            self.run_smt2(model::create(&self.ast))?;
        }
        Ok(())
    }

    pub fn sanity_check(&mut self) -> Result<(), VelosiSynthIssues> {
        self.create_model()?;

        log::info!(target: "[SynthZ3]", "running sanity checks on the model.");
        let mut issues = VelosiSynthIssues::new();

        issues.merge_result(vmops::sanity::check_precondition_satisfiability(
            self.workerpool.as_mut().unwrap(),
            &self.ast,
            "map",
        ));
        issues.merge_result(vmops::sanity::check_precondition_satisfiability(
            self.workerpool.as_mut().unwrap(),
            &self.ast,
            "unmap",
        ));
        issues.merge_result(vmops::sanity::check_precondition_satisfiability(
            self.workerpool.as_mut().unwrap(),
            &self.ast,
            "protect",
        ));

        synth_result_return!((), issues)
    }

    pub fn synthesize_all(&mut self) -> Result<SynthResult, VelosiSynthIssues> {
        // have this more conditional
        self.create_model()?;

        let z3 = self.workerpool.as_mut().unwrap();

        let batch_size = std::cmp::max(5, z3.num_workers() * 3 / 4);

        log::warn!("batch size: {}", batch_size);

        // --------------------------------------------------------------------------------------
        // Submit queries for all of the three vmops
        // --------------------------------------------------------------------------------------

        

        let t_start = Instant::now();

        let mut map_queries = vmops::map::get_program_iter(&self.ast, batch_size);
        let t_map = Instant::now();
        let mut unmap_queries = vmops::unmap::get_program_iter(&self.ast, batch_size);
        let t_unmap = Instant::now();
        let mut protect_queries = vmops::protect::get_program_iter(&self.ast, batch_size);

        let t_iters = Instant::now();

        let _diff = t_map.saturating_duration_since(t_start);

        log::info!("TIME:    map        unmap       protect      total");
        log::info!(
            "Iter      {}          {}           {}        {}",
            t_map.saturating_duration_since(t_start).as_millis(),
            t_unmap.saturating_duration_since(t_map).as_millis(),
            t_iters.saturating_duration_since(t_unmap).as_millis(),
            t_iters.saturating_duration_since(t_start).as_millis(),
        );

        let mut map_program = MaybeResult::Pending;
        let mut unmap_program = MaybeResult::Pending;
        let mut protect_program = MaybeResult::Pending;

        let mut all_done = true;
        loop {
            all_done = true;

            if map_program == MaybeResult::Pending {
                map_program = map_queries.next(z3);
                all_done &= map_program != MaybeResult::Pending
            }

            if unmap_program == MaybeResult::Pending {
                unmap_program = unmap_queries.next(z3);
                all_done &= unmap_program != MaybeResult::Pending
            }

            if protect_program == MaybeResult::Pending {
                protect_program = protect_queries.next(z3);
                all_done &= protect_program != MaybeResult::Pending
            }

            if all_done {
                break;
            }
        }

        debug_assert!(map_program != MaybeResult::Pending);
        debug_assert!(unmap_program != MaybeResult::Pending);
        debug_assert!(protect_program != MaybeResult::Pending);

        match (map_program, unmap_program, protect_program) {
            (MaybeResult::Some(mp), MaybeResult::Some(up), MaybeResult::Some(pp)) => {
                Ok(SynthResult {
                    map: mp,
                    unmap: up,
                    protect: pp,
                })
            }
            _ => Err(VelosiSynthIssues::new()),
        }
    }

    pub fn synthesize_map(&mut self) -> Result<Program, VelosiSynthIssues> {
        // have this more conditional
        self.create_model()?;

        vmops::map::synthesize(self.workerpool.as_mut().unwrap(), &self.ast)
    }

    pub fn synthesize_unmap(&mut self) -> Result<Program, VelosiSynthIssues> {
        // have this more conditional
        self.create_model()?;
        vmops::unmap::synthesize(self.workerpool.as_mut().unwrap(), &self.ast)
    }

    pub fn synthesize_protect(&mut self) -> Result<Program, VelosiSynthIssues> {
        // have this more conditional
        self.create_model()?;
        vmops::protect::synthesize(self.workerpool.as_mut().unwrap(), &self.ast)
    }
}
