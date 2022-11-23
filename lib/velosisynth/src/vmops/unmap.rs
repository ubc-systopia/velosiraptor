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

use std::collections::LinkedList;
use std::rc::Rc;
use std::time::Duration;

use velosiast::ast::{VelosiAstMethod, VelosiAstUnitSegment};

use crate::{programs::Program, z3::Z3WorkerPool, VelosiSynthIssues};

use super::{precond, utils};

use crate::vmops::precond::PrecondQueries;
use crate::vmops::queryhelper::MultiDimProgramQueries;
use crate::vmops::queryhelper::{MaybeResult, ProgramBuilder};
use crate::Z3Ticket;

use std::time::Instant;

pub struct UnmapPrograms {
    programs: MultiDimProgramQueries<PrecondQueries>,
    queries: LinkedList<(Program, [Option<Z3Ticket>; 2])>,
    candidates: Vec<Program>,

    m_fn: Rc<VelosiAstMethod>,
    t_fn: Rc<VelosiAstMethod>,
    f_fn: Rc<VelosiAstMethod>,
}

impl UnmapPrograms {
    pub fn new(
        programs: MultiDimProgramQueries<PrecondQueries>,
        m_fn: Rc<VelosiAstMethod>,
        t_fn: Rc<VelosiAstMethod>,
        f_fn: Rc<VelosiAstMethod>,
    ) -> Self {
        Self {
            programs,
            queries: LinkedList::new(),
            candidates: Vec::new(),
            m_fn,
            t_fn,
            f_fn,
        }
    }
}

impl ProgramBuilder for UnmapPrograms {
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
                if !has_work {
                    return MaybeResult::None;
                }
            }
        };

        // we have at least one candidate program
        const CONFIG_MAX_QUERIES: usize = 4;
        if self.queries.len() < CONFIG_MAX_QUERIES {
            if let Some(prog) = self.candidates.pop() {
                let translate_preconds = precond::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.t_fn.as_ref(),
                    None,
                    true,
                    prog.clone(),
                );

                let matchflags_preconds = precond::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.f_fn.as_ref(),
                    None,
                    true,
                    prog.clone(),
                );

                self.queries
                    .push_back((prog, [Some(translate_preconds), Some(matchflags_preconds)]));
            }
        }

        let mut res_program = None;
        let mut remaining_queries = LinkedList::new();
        while let Some((prog, mut tickets)) = self.queries.pop_front() {
            let mut all_done = true;
            for maybe_ticket in tickets.iter_mut() {
                if let Some(ticket) = maybe_ticket {
                    if let Some(mut result) = z3.get_result(*ticket) {
                        // we got a result, check if it's sat
                        let output = result.result();
                        if utils::check_result_no_rewrite(output) == utils::QueryResult::Sat {
                            // set the ticket to none to mark completion
                            *maybe_ticket = None;
                        } else {
                            // unsat result, just drop it
                            break;
                        }
                    } else {
                        all_done = false;
                    }
                }
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
        } else if !self.queries.is_empty() || !self.candidates.is_empty() {
            MaybeResult::Pending
        } else {
            debug_assert!(self.programs.next(z3) == MaybeResult::None);
            MaybeResult::None
        }
    }
}

pub fn get_program_iter(unit: &VelosiAstUnitSegment) -> UnmapPrograms {
    log::info!(
        target : "[synth::unmap]",
        "starting synthesizing the map operation"
    );

    // obtain the functions for the map operation
    let m_fn = unit.get_method("map").unwrap();
    let t_fn = unit.get_method("translate").unwrap();
    let f_fn = unit.get_method("matchflags").unwrap();

    // ---------------------------------------------------------------------------------------------
    // Translate: Add a query for each of the pre-conditions of the function
    // ---------------------------------------------------------------------------------------------

    let t_start = Instant::now();

    let map_queries = vec![
        precond::precond_query(unit, m_fn.clone(), t_fn.clone(), true),
        precond::precond_query(unit, m_fn.clone(), f_fn.clone(), true),
    ];
    let mut programs = MultiDimProgramQueries::new(map_queries);
    UnmapPrograms::new(programs, m_fn.clone(), t_fn.clone(), f_fn.clone())
}

pub fn synthesize(
    z3: &mut Z3WorkerPool,
    unit: &VelosiAstUnitSegment,
) -> Result<Program, VelosiSynthIssues> {
    let mut progs = get_program_iter(unit);
    loop {
        match progs.next(z3) {
            MaybeResult::Some(prog) => {
                println!("////////\n{}", prog);
            }
            MaybeResult::Pending => {
                // wait for a bit
                std::thread::sleep(Duration::from_millis(10));
            }
            MaybeResult::None => {
                panic!("no program found");
            }
        }
    }
    panic!("stop");
}
