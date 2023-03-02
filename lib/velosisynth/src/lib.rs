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
use std::sync::Arc;

use std::fmt::{Display, Formatter, Result as FmtResult};

// public re-exports

// crate modules
mod error;
mod model;
mod programs;
mod vmops;
mod z3;

use velosiast::ast::VelosiAstUnitSegment;

use crate::vmops::{MapPrograms, MaybeResult, ProgramBuilder, ProtectPrograms, UnmapPrograms};
pub use error::{VelosiSynthError, VelosiSynthIssues};
pub use programs::{Program, ProgramsBuilder, ProgramsIter};
pub use z3::{Z3Query, Z3TaskPriority, Z3Ticket, Z3Worker, Z3WorkerPool};

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

pub struct Z3Synth<'a> {
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
    model_created: bool,
}

impl<'a> Z3Synth<'a> {
    /// creates a new synthesis handle with the given worker poopl and the unit
    pub(crate) fn new(z3: Z3WorkerPool, unit: &'a mut VelosiAstUnitSegment) -> Self {
        let batch_size = std::cmp::max(DEFAULT_BATCH_SIZE, z3.num_workers());

        // XXX: move this to the the syntheisze() step.
        let map_queries = vmops::map::get_program_iter(unit, batch_size);
        let unmap_queries = vmops::unmap::get_program_iter(unit, batch_size);
        let protect_queries = vmops::protect::get_program_iter(unit, batch_size);

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
            model_created: false,
        }
    }

    fn destroy(self) -> &'a mut VelosiAstUnitSegment {
        self.unit
    }

    pub fn unit_ident(&self) -> &str {
        self.unit.ident()
    }

    /// creates the model for the synthesis for this handle
    pub fn create_model(&mut self) {
        if !self.model_created {
            self.model_created = true;
            let ctx = model::create(self.unit);
            self.z3.reset_with_context(Z3Query::from(ctx));
        }
    }

    pub fn sanity_check(&mut self) -> Result<(), VelosiSynthIssues> {
        self.create_model();

        log::info!(target: "[Z3Synth]", "running sanity checks on the model.");
        let mut issues = VelosiSynthIssues::new();

        issues.merge_result(vmops::sanity::check_precondition_satisfiability(
            &mut self.z3,
            self.unit,
            "map",
        ));
        issues.merge_result(vmops::sanity::check_precondition_satisfiability(
            &mut self.z3,
            self.unit,
            "unmap",
        ));
        issues.merge_result(vmops::sanity::check_precondition_satisfiability(
            &mut self.z3,
            self.unit,
            "protect",
        ));

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
            log::warn!(target : "[Z3Synth]", "successfully synthesized program\nmap() {{ {} }}", prog);
            unit.set_method_ops("map", prog.into());
        } else {
            log::warn!(target : "[Z3Synth]", "map() {{ UNKNOWN }} ");
        }

        if let Some(prog) = unmap_program {
            log::warn!(target : "[Z3Synth]", "successfully synthesized program\nunmap() {{ {} }}", prog);
            unit.set_method_ops("unmap", prog.into());
        } else {
            log::warn!(target : "[Z3Synth]", "unmap() {{ UNKNOWN }}");
        }

        if let Some(prog) = protect_program {
            log::warn!(target : "[Z3Synth]", "successfully synthesized program\nprotect() {{ {} }}", prog);
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
        if self.done {
            return;
        }

        // create the model of not done yet
        self.create_model();

        let mut all_done = true;

        if self.map_program.is_none() {
            match self.map_queries.next(&mut self.z3) {
                MaybeResult::Some(mp) => {
                    all_done &= true;
                    self.map_program = Some(mp);
                }
                MaybeResult::Pending => all_done = false,
                MaybeResult::None => {
                    all_done = true;
                    self.map_program = Some(Program::new());
                }
            }
        }

        if self.unmap_program.is_none() {
            match self.unmap_queries.next(&mut self.z3) {
                MaybeResult::Some(mp) => {
                    all_done &= true;
                    self.unmap_program = Some(mp);
                }
                MaybeResult::Pending => all_done = false,
                MaybeResult::None => {
                    all_done = true;
                    self.unmap_program = Some(Program::new());
                }
            }
        }

        if self.protect_program.is_none() {
            match self.protect_queries.next(&mut self.z3) {
                MaybeResult::Some(mp) => {
                    all_done &= true;
                    self.protect_program = Some(mp);
                }
                MaybeResult::Pending => all_done = false,
                MaybeResult::None => {
                    all_done = true;
                    self.protect_program = Some(Program::new());
                }
            }
        }

        // update the all done flag
        self.done = all_done;

        // if we are done, terminate the worker pool
        if all_done {
            self.terminate();
        }
    }

    /// synthesizes the program for the unit, returns when done
    pub fn synthesize(&mut self) {
        while !self.is_done() {
            self.synthesize_step();
        }
    }

    pub fn synthesize_map(&mut self) -> Result<Program, VelosiSynthIssues> {
        // have this more conditional
        self.create_model();
        self.done = true;
        vmops::map::synthesize(&mut self.z3, self.unit)
    }

    pub fn synthesize_unmap(&mut self) -> Result<Program, VelosiSynthIssues> {
        // have this more conditional
        self.create_model();
        self.done = true;
        vmops::unmap::synthesize(&mut self.z3, self.unit)
    }

    pub fn synthesize_protect(&mut self) -> Result<Program, VelosiSynthIssues> {
        // have this more conditional
        self.create_model();
        self.done = true;
        vmops::protect::synthesize(&mut self.z3, self.unit)
    }

    /// terminates the worker pool
    pub fn terminate(&mut self) {
        self.z3.terminate();
    }
}

impl<'a> Display for Z3Synth<'a> {
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
            num_workers: 1,
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

    pub fn create<'a>(&self, unit: &'a mut VelosiAstUnitSegment) -> Z3Synth<'a> {
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
        Z3Synth::new(z3, unit)
    }
}

impl Default for Z3SynthFactory {
    fn default() -> Self {
        Self::new()
    }
}
