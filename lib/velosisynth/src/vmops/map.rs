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

use std::collections::LinkedList;
use std::rc::Rc;
use std::time::Duration;

use velosiast::ast::{VelosiAstMethod, VelosiAstUnitSegment};

use crate::{programs::Program, z3::Z3WorkerPool, VelosiSynthIssues};

use super::{precond, semantics, utils};

use crate::vmops::precond::PrecondQueries;
use crate::vmops::queryhelper::MultiDimProgramQueries;
use crate::vmops::queryhelper::ProgramQueries;
use crate::vmops::queryhelper::{MaybeResult, ProgramBuilder};
use crate::vmops::semantics::SemanticQueries;
use crate::Z3Ticket;

pub enum PartQueries {
    Precond(PrecondQueries),
    Semantic(ProgramQueries<SemanticQueries>),
}

impl ProgramBuilder for PartQueries {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        match self {
            Self::Precond(q) => q.next(z3),
            Self::Semantic(q) => q.next(z3),
        }
    }
}

pub struct MapPrograms {
    programs: MultiDimProgramQueries<PartQueries>,
    programs_done: bool,
    queries: LinkedList<(Program, [Option<Z3Ticket>; 4])>,
    candidates: Vec<Program>,

    m_fn: Rc<VelosiAstMethod>,
    t_fn: Rc<VelosiAstMethod>,
    f_fn: Rc<VelosiAstMethod>,
}

impl MapPrograms {
    pub fn new(
        programs: MultiDimProgramQueries<PartQueries>,
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

impl ProgramBuilder for MapPrograms {
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
                let translate_preconds = precond::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.t_fn.as_ref(),
                    None,
                    false,
                    prog.clone(),
                );
                let translate_semantics = semantics::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.t_fn.as_ref(),
                    None,
                    prog.clone(),
                    false,
                );

                let matchflags_preconds = precond::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.f_fn.as_ref(),
                    None,
                    false,
                    prog.clone(),
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
                    [
                        Some(translate_preconds),
                        Some(translate_semantics),
                        Some(matchflags_preconds),
                        Some(matchflags_semantics),
                    ],
                ));
            }
        }

        let mut res_program = None;
        let mut remaining_queries = LinkedList::new();
        while let Some((prog, mut tickets)) = self.queries.pop_front() {
            let mut all_done = true;
            for maybe_ticket in tickets.iter_mut() {
                if let Some(ticket) = maybe_ticket {
                    if let Some(result) = z3.get_result(*ticket) {
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
        } else if !self.queries.is_empty() || !self.candidates.is_empty() || !self.programs_done {
            MaybeResult::Pending
        } else {
            debug_assert!(self.programs.next(z3) == MaybeResult::None);
            MaybeResult::None
        }
    }
}

pub fn get_program_iter(unit: &VelosiAstUnitSegment, batch_size: usize) -> MapPrograms {
    log::info!(
        target : "[synth::map]",
        "starting synthesizing the map operation"
    );

    // obtain the functions for the map operation
    let m_fn = unit.get_method("map").unwrap();
    let t_fn = unit.get_method("translate").unwrap();
    let f_fn = unit.get_method("matchflags").unwrap();

    // ---------------------------------------------------------------------------------------------
    // Translate: Add a query for each of the pre-conditions of the function
    // ---------------------------------------------------------------------------------------------

    let map_queries = vec![
        PartQueries::Precond(precond::precond_query(
            unit,
            m_fn.clone(),
            t_fn.clone(),
            false,
            batch_size,
        )),
        PartQueries::Precond(precond::precond_query(
            unit,
            m_fn.clone(),
            f_fn.clone(),
            false,
            batch_size,
        )),
        PartQueries::Semantic(semantics::semantic_query(
            unit,
            m_fn.clone(),
            t_fn.clone(),
            false,
            batch_size,
        )),
        PartQueries::Semantic(semantics::semantic_query(
            unit,
            m_fn.clone(),
            f_fn.clone(),
            false,
            batch_size,
        )),
    ];
    let programs = MultiDimProgramQueries::new(map_queries);

    MapPrograms::new(programs, m_fn.clone(), t_fn.clone(), f_fn.clone())
}

pub fn synthesize(
    z3: &mut Z3WorkerPool,
    unit: &VelosiAstUnitSegment,
) -> Result<Program, VelosiSynthIssues> {
    let batch_size = std::cmp::max(5, z3.num_workers() / 2);
    let mut mprogs = get_program_iter(unit, batch_size);
    loop {
        match mprogs.next(z3) {
            MaybeResult::Some(prog) => {
                return Ok(prog);
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
}
