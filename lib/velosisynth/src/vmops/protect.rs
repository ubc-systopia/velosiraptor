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

//! Synthesis of Virtual Memory Operations: Protect

use std::collections::LinkedList;
use std::rc::Rc;

use velosiast::ast::{VelosiAstMethod, VelosiAstUnitSegment};

use crate::error::VelosiSynthErrorBuilder;
use crate::{programs::Program, z3::Z3WorkerPool, VelosiSynthIssues};

use super::{semantics, utils};

use crate::vmops::queryhelper::MultiDimProgramQueries;
use crate::vmops::queryhelper::ProgramQueries;
use crate::vmops::queryhelper::{MaybeResult, ProgramBuilder};
use crate::vmops::semantics::SemanticQueries;
use crate::Z3Ticket;

pub struct ProtectPrograms {
    programs: MultiDimProgramQueries<ProgramQueries<SemanticQueries>>,
    programs_done: bool,

    queries: LinkedList<(Program, [Option<Z3Ticket>; 2])>,
    candidates: Vec<Program>,

    m_fn: Rc<VelosiAstMethod>,
    t_fn: Rc<VelosiAstMethod>,
    f_fn: Rc<VelosiAstMethod>,
}

impl ProtectPrograms {
    pub fn new(
        programs: MultiDimProgramQueries<ProgramQueries<SemanticQueries>>,
        m_fn: Rc<VelosiAstMethod>,
        t_fn: Rc<VelosiAstMethod>,
        f_fn: Rc<VelosiAstMethod>,
    ) -> Self {
        Self {
            programs,
            programs_done: false,
            queries: LinkedList::new(),
            candidates: Vec::new(),
            m_fn,
            t_fn,
            f_fn,
        }
    }
}

impl ProgramBuilder for ProtectPrograms {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        let has_work = !self.candidates.is_empty() || !self.queries.is_empty();

        // poll once, collect the program
        match self.programs.next(z3) {
            MaybeResult::Some(p) => self.candidates.push(p),
            MaybeResult::Pending => {
                if !has_work {
                    return MaybeResult::Pending;
                }
            }
            MaybeResult::None => {
                self.programs_done = true;
                if !has_work {
                    return MaybeResult::None;
                }
            }
        };

        // we have at least one candidate program
        const CONFIG_MAX_QUERIES: usize = 4;
        if self.queries.len() < CONFIG_MAX_QUERIES {
            if let Some(prog) = self.candidates.pop() {
                let translate_semantics = semantics::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.t_fn.as_ref(),
                    None,
                    prog.clone(),
                    true,
                );

                let matchflags_semantics = semantics::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.f_fn.as_ref(),
                    None,
                    prog.clone(),
                    false,
                );

                self.queries.push_back((
                    prog,
                    [Some(translate_semantics), Some(matchflags_semantics)],
                ));
            }
        }

        let mut res_program = None;
        let mut remaining_queries = LinkedList::new();
        while let Some((prog, mut tickets)) = self.queries.pop_front() {
            let mut all_done = true;
            let mut unsat_part = false;
            for (_i, maybe_ticket) in tickets.iter_mut().enumerate() {
                if let Some(ticket) = maybe_ticket {
                    if let Some(result) = z3.get_result(*ticket) {
                        // we got a result, check if it's sat
                        let output = result.result();
                        if utils::check_result_no_rewrite(output) == utils::QueryResult::Sat {
                            // set the ticket to none to mark completion
                            *maybe_ticket = None;
                            // record that we've found a program that satisfies the first query
                        } else {
                            // unsat result, just drop it
                            unsat_part = true;
                            break;
                        }
                    } else {
                        all_done = false;
                    }
                }
            }

            if unsat_part {
                // drop the program and the tickets as it contains one unsar part
                continue;
            }

            // store the result
            if all_done && res_program.is_none() {
                res_program = Some(prog);
            } else {
                remaining_queries.push_back((prog, tickets));
            }
        }

        self.queries = remaining_queries;

        if let Some(prog) = res_program {
            MaybeResult::Some(prog)
        } else if !self.queries.is_empty() || !self.candidates.is_empty() || !self.programs_done {
            MaybeResult::Pending
        } else {
            debug_assert!(self.programs.next(z3) == MaybeResult::None);
            MaybeResult::None
        }
    }
}

pub fn get_program_iter(unit: &VelosiAstUnitSegment, batch_size: usize) -> ProtectPrograms {
    log::info!(
        target : "[synth::protect]",
        "starting synthesizing the protect operation"
    );

    // obtain the functions for the map operation
    let m_fn = unit.get_method("protect").unwrap();
    let t_fn = unit.get_method("translate").unwrap();
    let f_fn = unit.get_method("matchflags").unwrap();

    // ---------------------------------------------------------------------------------------------
    // Translate: Add a query for each of the pre-conditions of the function
    // ---------------------------------------------------------------------------------------------

    let mut protec_queries = Vec::with_capacity(2);

    if let Some(p) =
        semantics::semantic_query(unit, m_fn.clone(), t_fn.clone(), f_fn, true, batch_size).take()
    {
        protec_queries.push(p);
    }

    if let Some(p) =
        semantics::semantic_query(unit, m_fn.clone(), f_fn.clone(), f_fn, false, batch_size).take()
    {
        protec_queries.push(p);
    }

    let programs = MultiDimProgramQueries::new(protec_queries);

    ProtectPrograms::new(programs, m_fn.clone(), t_fn.clone(), f_fn.clone())
}

pub fn synthesize(
    z3: &mut Z3WorkerPool,
    unit: &VelosiAstUnitSegment,
) -> Result<Program, VelosiSynthIssues> {
    let batch_size = std::cmp::max(5, z3.num_workers() / 2);
    let mut progs = get_program_iter(unit, batch_size);
    loop {
        match progs.next(z3) {
            MaybeResult::Some(prog) => return Ok(prog),
            MaybeResult::Pending => {
                // just keep running
            }
            MaybeResult::None => {
                break;
            }
        }
    }

    let m_fn = unit.get_method("protect").unwrap();
    let msg = "failed to synthesize a program for the protect operation";
    let err = VelosiSynthErrorBuilder::err(msg.to_string())
        .add_location(m_fn.loc.clone())
        .build();

    Err(err.into())
}
