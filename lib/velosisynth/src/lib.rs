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

use std::collections::HashMap;
use std::env;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;
use std::time::{Duration, Instant};

// public re-exports

// crate modules
mod error;
mod model;
mod programs;
mod sanitycheck;
mod vmops;
mod z3;

use smt2::{Smt2Context, Smt2Option};
use velosiast::VelosiAst;
use velosiast::{ast::VelosiAstUnitSegment, VelosiAstUnitEnum};

use crate::vmops::{
    enums, MapPrograms, MaybeResult, ProgramBuilder, ProtectPrograms, UnmapPrograms,
};
pub use error::{VelosiSynthError, VelosiSynthIssues};
pub use programs::{Program, ProgramsBuilder, ProgramsIter};
pub use z3::{Z3Query, Z3TaskPriority, Z3Ticket, Z3Worker, Z3WorkerPool, Z3WorkerPoolStats};

const DEFAULT_BATCH_SIZE: usize = 32;

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

pub struct Z3SynthSegment<'a> {
    z3: Z3WorkerPool,
    // unit: Option<Rc<VelosiAstUnitSegment>>,
    unit: &'a mut VelosiAstUnitSegment,
    map_queries: MapPrograms,
    map_program: Option<Program>,
    unmap_queries: UnmapPrograms,
    unmap_program: Option<Program>,
    protect_queries: ProtectPrograms,
    protect_program: Option<Program>,
    done: bool,

    // stats
    /// runtime for the sanity check
    pub t_sanity_check: Duration,
    /// the time to synthesize the map program
    pub t_map_synthesis: Duration,
    /// the time to synthesize the unmap program
    pub t_unmap_synthesis: Duration,
    /// the time to synthesize the protect program
    pub t_protect_synthesis: Duration,
    /// the point in time when the synthesis started
    t_synth_start: Option<Instant>,
}

impl<'a> Z3SynthSegment<'a> {
    /// creates a new synthesis handle with the given worker poopl and the unit
    pub(crate) fn new(
        mut z3: Z3WorkerPool,
        unit: &'a mut VelosiAstUnitSegment,
        model: Arc<Smt2Context>,
    ) -> Self {
        let batch_size = std::cmp::max(DEFAULT_BATCH_SIZE, z3.num_workers());

        // XXX: move this to the the syntheisze() step.
        let map_queries = vmops::map::get_program_iter(unit, batch_size, None);
        let unmap_queries = vmops::unmap::get_program_iter(unit, batch_size, None);
        let protect_queries = vmops::protect::get_program_iter(unit, batch_size, None);

        z3.reset_with_context(Z3Query::with_contexts(vec![model]));

        Self {
            z3,
            unit,
            map_queries,
            map_program: None,
            unmap_queries,
            unmap_program: None,
            protect_queries,
            protect_program: None,
            done: false,
            t_sanity_check: Duration::from_secs(0),
            t_map_synthesis: Duration::from_secs(0),
            t_unmap_synthesis: Duration::from_secs(0),
            t_protect_synthesis: Duration::from_secs(0),
            t_synth_start: None,
        }
    }

    fn destroy(self) -> &'a mut VelosiAstUnitSegment {
        self.unit
    }

    pub fn unit_ident(&self) -> &str {
        self.unit.ident()
    }

    pub fn sanity_check(&mut self) -> Result<(), VelosiSynthIssues> {
        let t_start = Instant::now();

        log::warn!(target: "[Z3Synth]", "running sanity checks on the model.");
        let _issues = VelosiSynthIssues::new();

        // first make sure the methods themselves are sane
        let issues = sanitycheck::check_methods(&mut self.z3, self.unit);
        if !issues.is_ok() {
            self.t_sanity_check = Instant::now() - t_start;
            return synth_result_return!((), issues);
        }

        // now make sure the unit is sane
        let issues = sanitycheck::check_unit(&mut self.z3, self.unit);
        self.t_sanity_check = Instant::now() - t_start;

        synth_result_return!((), issues)
    }

    pub fn finalize(mut self) -> Result<bool, Self> {
        if !self.is_done() {
            log::error!("called finalize() but synthesis is not done yet.");
            return Err(self);
        }

        // obtain the programs and drop the references
        let map_program = self.map_program.take();
        let unmap_program = self.unmap_program.take();
        let protect_program = self.protect_program.take();
        let unit = self.destroy();

        if let Some(prog) = map_program {
            log::info!(target : "[Z3Synth]", "successfully synthesized program\n{}.map() {{ {} }}", unit.ident(), prog);
            unit.set_method_ops("map", prog.into());
        } else {
            log::warn!(target : "[Z3Synth]", "map() {{ UNKNOWN }} ");
        }

        if let Some(prog) = unmap_program {
            log::info!(target : "[Z3Synth]", "successfully synthesized program\n{}.unmap() {{ {} }}", unit.ident(), prog);
            unit.set_method_ops("unmap", prog.into());
        } else {
            log::warn!(target : "[Z3Synth]", "unmap() {{ UNKNOWN }}");
        }

        if let Some(prog) = protect_program {
            log::info!(target : "[Z3Synth]", "successfully synthesized program\n{}.protect() {{ {} }}", unit.ident(),prog);
            unit.set_method_ops("protect", prog.into());
        } else {
            log::warn!(target : "[Z3Synth]", "protect() {{ UNKNOWN }}");
        }

        Ok(true)
    }

    /// checks whether the synthesis has completed, either with result or not
    pub fn is_done(&self) -> bool {
        self.done
    }

    /// checks whether we have a result
    pub fn has_result(&self) -> bool {
        self.is_done()
            && self.map_program.is_some()
            && self.unmap_program.is_some()
            && self.protect_program.is_some()
    }

    /// performs a synthesis step for all operations that haven't completed yet
    pub fn synthesize_step(&mut self) {
        if self.t_synth_start.is_none() {
            self.t_synth_start = Some(Instant::now());
        }

        if self.done {
            return;
        }

        let t_synth_start = self.t_synth_start.unwrap();

        let mut all_done = true;

        if self.map_program.is_none() {
            match self.map_queries.next(&mut self.z3) {
                MaybeResult::Some(mp) => {
                    all_done &= true;
                    self.map_program = Some(mp);
                    self.t_map_synthesis = Instant::now() - t_synth_start;
                }
                MaybeResult::Pending => all_done = false,
                MaybeResult::None => {
                    all_done = true;
                    log::warn!("did not find a map program");
                    self.map_program = Some(Program::new());
                    self.t_map_synthesis = Instant::now() - t_synth_start;
                }
            }
        }

        if self.unmap_program.is_none() {
            match self.unmap_queries.next(&mut self.z3) {
                MaybeResult::Some(mp) => {
                    all_done &= true;
                    self.unmap_program = Some(mp);
                    self.t_unmap_synthesis = Instant::now() - t_synth_start;
                }
                MaybeResult::Pending => all_done = false,
                MaybeResult::None => {
                    all_done = true;
                    log::warn!("did not find a unmap program");
                    self.unmap_program = Some(Program::new());
                    self.t_unmap_synthesis = Instant::now() - t_synth_start;
                }
            }
        }

        if self.protect_program.is_none() {
            match self.protect_queries.next(&mut self.z3) {
                MaybeResult::Some(mp) => {
                    all_done &= true;
                    self.protect_program = Some(mp);
                    self.t_protect_synthesis = Instant::now() - t_synth_start;
                }
                MaybeResult::Pending => all_done = false,
                MaybeResult::None => {
                    log::warn!("did not find a protect program");
                    all_done = true;
                    self.protect_program = Some(Program::new());
                    self.t_protect_synthesis = Instant::now() - t_synth_start;
                }
            }
        }

        // update the all done flag
        self.done = all_done;
    }

    /// synthesizes the program for the unit, returns when done
    pub fn synthesize(&mut self, mem_model: bool) {
        while !self.is_done() {
            self.synthesize_step();
        }

        if mem_model && self.has_result() {
            self.done = false;

            // generate the new z3 model, taking into account the memory model
            let ctx = model::create(self.unit, true);
            self.z3.reset_with_context(Z3Query::from(ctx));

            let unit = &self.unit;
            let batch_size = std::cmp::max(DEFAULT_BATCH_SIZE, self.z3.num_workers());

            // use the previously generated programs as a starting point
            self.map_queries =
                vmops::map::get_program_iter(unit, batch_size, self.map_program.take());
            self.unmap_queries =
                vmops::unmap::get_program_iter(unit, batch_size, self.unmap_program.take());
            self.protect_queries =
                vmops::protect::get_program_iter(unit, batch_size, self.protect_program.take());

            // do the synthesis step again
            while !self.is_done() {
                self.synthesize_step();
            }
        }
    }

    pub fn synthesize_map(&mut self, mem_model: bool) -> Result<Program, VelosiSynthIssues> {
        self.done = true;

        let prog = vmops::map::synthesize(&mut self.z3, self.unit, None)?;
        if mem_model {
            let ctx = model::create(self.unit, true);
            self.z3.reset_with_context(Z3Query::from(ctx));

            vmops::map::synthesize(&mut self.z3, self.unit, Some(prog))
        } else {
            Ok(prog)
        }
    }

    pub fn synthesize_unmap(&mut self, mem_model: bool) -> Result<Program, VelosiSynthIssues> {
        self.done = true;

        let prog = vmops::unmap::synthesize(&mut self.z3, self.unit, None)?;
        if mem_model {
            let ctx = model::create(self.unit, true);
            self.z3.reset_with_context(Z3Query::from(ctx));

            vmops::unmap::synthesize(&mut self.z3, self.unit, Some(prog))
        } else {
            Ok(prog)
        }
    }

    pub fn synthesize_protect(&mut self, mem_model: bool) -> Result<Program, VelosiSynthIssues> {
        self.done = true;

        let prog = vmops::protect::synthesize(&mut self.z3, self.unit, None)?;
        if mem_model {
            let ctx = model::create(self.unit, true);
            self.z3.reset_with_context(Z3Query::from(ctx));

            vmops::protect::synthesize(&mut self.z3, self.unit, Some(prog))
        } else {
            Ok(prog)
        }
    }

    /// terminates the worker pool
    pub fn terminate(&mut self) {
        self.z3.terminate();
    }

    pub fn worker_pool_stats(&self) -> &Z3WorkerPoolStats {
        self.z3.stats()
    }
}

impl<'a> Display for Z3SynthSegment<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if self.is_done() {
            if let Some(prog) = &self.map_program {
                writeln!(f, "map: {prog}")?;
            } else {
                writeln!(f, "map: synthesis failed")?;
            }

            if let Some(prog) = &self.unmap_program {
                writeln!(f, "unmap: {prog}")?;
            } else {
                writeln!(f, "unmap: synthesis failed")?;
            }

            if let Some(prog) = &self.protect_program {
                writeln!(f, "protect: {prog}")
            } else {
                writeln!(f, "protect: synthesis failed")
            }
        } else {
            write!(f, "Synthesis not done yet.")
        }
    }
}

pub struct Z3SynthEnum<'a> {
    z3: Z3WorkerPool,
    unit: &'a mut VelosiAstUnitEnum,
}

impl<'a> Z3SynthEnum<'a> {
    pub fn new(z3: Z3WorkerPool, unit: &'a mut VelosiAstUnitEnum) -> Self {
        Self { z3, unit }
    }

    pub fn distinguish(&mut self, models: &HashMap<Rc<String>, Arc<Smt2Context>>) {
        let mut prelude = Smt2Context::new();
        prelude.set_option(Smt2Option::ProduceUnsatCores(true));

        let mut contexts = vec![Arc::new(prelude)];
        models
            .iter()
            .filter(|(ident, _)| self.unit.get_unit_names().contains(ident))
            .for_each(|(_, ctx)| contexts.push(ctx.clone()));

        self.z3.reset_with_context(Z3Query::with_contexts(contexts));
        enums::distinguish(&mut self.z3, self.unit)
    }
}

/// Represents a
pub struct Z3SynthFactory {
    /// the output directory for the synthesis logs
    logdir: Option<Arc<PathBuf>>,
    /// whether logging is enabled or not
    logging: bool,
    /// the number of workers to use
    num_workers: usize,
}

impl Z3SynthFactory {
    /// initializes a new Z3 Synthesis engine with the default number of workers and log
    pub fn new() -> Self {
        Self {
            logdir: None,
            logging: cfg!(debug_assertions),
            num_workers: std::cmp::max(
                1usize,
                std::thread::available_parallelism()
                    .map(|i| i.into())
                    .unwrap_or(1)
                    - 1,
            ),
        }
    }

    pub fn logdir(&mut self, logdir: Arc<PathBuf>) -> &mut Self {
        self.logdir = Some(logdir);
        self
    }

    pub fn logging(&mut self, logging: bool) -> &mut Self {
        self.logging = logging;
        self
    }

    pub fn default_log_dir(&mut self) -> &mut Self {
        if cfg!(debug_assertions) {
            // get the outdir from the current path
            let outdir = env::current_dir().unwrap();
            let outdir = outdir.join("logs");

            self.logdir = Some(Arc::new(outdir));
        }
        self
    }

    pub fn num_workers(&mut self, num_workers: usize) -> &mut Self {
        self.num_workers = num_workers;
        self
    }

    pub fn create_segment<'a>(
        &self,
        unit: &'a mut VelosiAstUnitSegment,
        model: Arc<Smt2Context>,
    ) -> Z3SynthSegment<'a> {
        if unit.is_abstract {
            panic!("Cannot synthesize abstract units");
        }

        let logpath = if let Some(logdir) = &self.logdir {
            if self.logging {
                Some(Arc::new(logdir.join(unit.ident().as_str())))
            } else {
                None
            }
        } else {
            None
        };

        let z3 = Z3WorkerPool::with_num_workers(self.num_workers, logpath);
        Z3SynthSegment::new(z3, unit, model)
    }

    pub fn create_enum<'a>(&self, unit: &'a mut VelosiAstUnitEnum) -> Z3SynthEnum<'a> {
        let logpath = if let Some(logdir) = &self.logdir {
            if self.logging {
                Some(Arc::new(logdir.join(unit.ident().as_str())))
            } else {
                None
            }
        } else {
            None
        };

        let z3 = Z3WorkerPool::with_num_workers(self.num_workers, logpath);
        Z3SynthEnum::new(z3, unit)
    }
}

impl Default for Z3SynthFactory {
    fn default() -> Self {
        Self::new()
    }
}

pub fn create_models(ast: &VelosiAst) -> HashMap<Rc<String>, Arc<Smt2Context>> {
    ast.segments()
        .iter()
        .map(|u| (u.ident().clone(), Arc::new(model::create(u, false))))
        .collect()
}
