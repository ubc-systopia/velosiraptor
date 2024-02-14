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

//! Synthesis of Virtual Memory Operations

pub mod enums;
mod map;
mod protect;
mod queries;
mod unmap;

use std::rc::Rc;

// re-export the sanity checks
// pub use queries::resultparser;
// pub use queries::utils;

// reexport the program synthesis wrappers
pub use map::MapPrograms;
pub use protect::ProtectPrograms;
pub use unmap::UnmapPrograms;

/// re-export the query builder stuff
pub use queries::{
    BoolExprQuery, BoolExprQueryBuilder, CompoundBoolExprQueryBuilder, CompoundQueryAll,
    CompoundQueryAny, MaybeResult, ProgramBuilder, ProgramVerifier, TranslateQuery,
    TranslateQueryBuilder,
};

use velosiast::ast::VelosiAstUnitSegment;

use crate::model;
use crate::opts::SynthOpts;
use crate::z3::{Z3Query, Z3WorkerPool};
use crate::Program;

pub trait SynchronousSync<T: ProgramBuilder = Self>: ProgramBuilder {
    fn do_synthesize(&mut self, z3: &mut Z3WorkerPool) -> Option<Program> {
        loop {
            match self.next(z3) {
                MaybeResult::Some(prog) => return Some(prog),
                MaybeResult::Pending => continue,
                MaybeResult::None => return None,
            }
        }
    }

    fn synthesize(
        &mut self,
        z3: &mut Z3WorkerPool,
        unit: &VelosiAstUnitSegment,
        batch_size: usize,
        mem_model: bool,
    ) -> Option<Program> {
        let ctx = model::create(unit, false);
        z3.reset_with_context(Z3Query::from(ctx), false);

        // let mut programs = MapPrograms::new(unit, batch_size, None);
        if let Some(prog) = self.do_synthesize(z3) {
            if mem_model {
                let ctx = model::create(unit, false);
                z3.reset_with_context(Z3Query::from(ctx), false);

                let mut programs = MapPrograms::with_opts(
                    unit,
                    SynthOpts::with_batchsize(batch_size),
                    Some(Rc::new(prog)),
                );
                programs.do_synthesize(z3)
            } else {
                Some(prog)
            }
        } else {
            None
        }
    }
}
