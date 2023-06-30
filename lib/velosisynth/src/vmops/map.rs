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

use velosiast::ast::{VelosiAstMethod, VelosiAstUnitSegment};

use crate::ProgramsIter;
use crate::{programs::Program, z3::Z3WorkerPool, VelosiSynthIssues};

use super::{precond, semantics, semprecond, utils};

use super::queryhelper::PartQueries;
use crate::vmops::queryhelper::MultiDimProgramQueries;
use crate::vmops::queryhelper::{MaybeResult, ProgramBuilder};
use crate::vmops::utils::SynthOptions;
use crate::Z3Ticket;
use crate::DEFAULT_BATCH_SIZE;

pub enum MapProgramQueries {
    SingleQuery(ProgramsIter),
    MultiQuery(MultiDimProgramQueries<PartQueries>),
}

impl ProgramBuilder for MapProgramQueries {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        match self {
            Self::SingleQuery(q) => q.next(z3),
            Self::MultiQuery(q) => q.next(z3),
        }
    }
}

pub struct MapPrograms {
    programs: MapProgramQueries,
    programs_done: bool,
    queries: LinkedList<(Program, [Option<Z3Ticket>; 6])>,
    candidates: Vec<Program>,

    m_fn: Rc<VelosiAstMethod>,
    v_fn: Rc<VelosiAstMethod>,
    t_fn: Rc<VelosiAstMethod>,
    f_fn: Rc<VelosiAstMethod>,

    mem_model: bool,
}

impl MapPrograms {
    pub fn new(
        programs: MapProgramQueries,
        m_fn: Rc<VelosiAstMethod>,
        v_fn: Rc<VelosiAstMethod>,
        t_fn: Rc<VelosiAstMethod>,
        f_fn: Rc<VelosiAstMethod>,
        mem_model: bool,
    ) -> Self {
        Self {
            programs,
            programs_done: false,
            queries: LinkedList::new(),
            candidates: Vec::new(),
            m_fn,
            v_fn,
            t_fn,
            f_fn,
            mem_model,
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
                let valid_semantics = semantics::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.v_fn.as_ref(),
                    None,
                    prog.clone(),
                    SynthOptions {
                        negate: false,
                        no_change: false,
                        mem_model: self.mem_model,
                    },
                );

                let translate_preconds = precond::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.t_fn.as_ref(),
                    None,
                    false,
                    prog.clone(),
                    self.mem_model,
                );
                let translate_semantics = semantics::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.t_fn.as_ref(),
                    None,
                    prog.clone(),
                    SynthOptions {
                        negate: false,
                        no_change: false,
                        mem_model: self.mem_model,
                    },
                );

                let matchflags_preconds = precond::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.f_fn.as_ref(),
                    None,
                    false,
                    prog.clone(),
                    self.mem_model,
                );
                let matchflags_semantics = semantics::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.f_fn.as_ref(),
                    None,
                    prog.clone(),
                    SynthOptions {
                        negate: false,
                        no_change: false,
                        mem_model: self.mem_model,
                    },
                );

                let semprodoncs = semprecond::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.t_fn.as_ref(),
                    None,
                    prog.clone(),
                    SynthOptions {
                        negate: false,
                        no_change: false,
                        mem_model: self.mem_model,
                    },
                );

                self.queries.push_back((
                    prog,
                    [
                        Some(semprodoncs),
                        Some(valid_semantics),
                        Some(translate_semantics),
                        Some(matchflags_semantics),
                        Some(translate_preconds),
                        Some(matchflags_preconds),
                    ],
                ));
            }
        }

        let mut res_program = None;
        let mut remaining_queries = LinkedList::new();
        'outer: while let Some((prog, mut tickets)) = self.queries.pop_front() {
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
                            // unsat result, just drop the program and the tickets
                            continue 'outer;
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

pub fn get_program_iter(
    unit: &VelosiAstUnitSegment,
    batch_size: usize,
    starting_prog: Option<Program>,
) -> MapPrograms {
    log::info!(
        target : "[synth::map]",
        "starting synthesizing the map operation"
    );

    // obtain the functions for the map operation
    let m_fn = unit
        .get_method("map")
        .unwrap_or_else(|| panic!("no method 'map' in unit {}", unit.ident()));
    let v_fn = unit.get_method("valid").unwrap();
    let t_fn = unit.get_method("translate").unwrap();
    let f_fn = unit.get_method("matchflags").unwrap();

    if let Some(prog) = starting_prog {
        // ---------------------------------------------------------------------------------------------
        // Translate: Add a query for each possible barrier position
        // ---------------------------------------------------------------------------------------------
        MapPrograms::new(
            MapProgramQueries::SingleQuery(utils::make_program_iter_mem(prog)),
            m_fn.clone(),
            v_fn.clone(),
            t_fn.clone(),
            f_fn.clone(),
            true,
        )
    } else {
        // ---------------------------------------------------------------------------------------------
        // Translate: Add a query for each of the pre-conditions of the function
        // ---------------------------------------------------------------------------------------------

        let mut map_queries = Vec::new();
        if let Some(p) = precond::precond_query(unit, m_fn.clone(), t_fn.clone(), false, batch_size)
        {
            map_queries.push(PartQueries::Precond(p));
        }

        if let Some(p) = precond::precond_query(unit, m_fn.clone(), f_fn.clone(), false, batch_size)
        {
            map_queries.push(PartQueries::Precond(p));
        }

        if let Some(p) =
            semprecond::semprecond_query(unit, m_fn.clone(), t_fn.clone(), false, batch_size)
        {
            map_queries.push(PartQueries::SemPrecond(p));
        }

        if let Some(p) = semantics::semantic_query(
            unit,
            m_fn.clone(),
            v_fn.clone(),
            v_fn,
            false,
            false,
            batch_size,
        ) {
            map_queries.push(PartQueries::Semantic(p));
        }

        if let Some(p) = semantics::semantic_query(
            unit,
            m_fn.clone(),
            t_fn.clone(),
            t_fn,
            false,
            false,
            batch_size,
        ) {
            map_queries.push(PartQueries::Semantic(p));
        }

        if let Some(p) = semantics::semantic_query(
            unit,
            m_fn.clone(),
            f_fn.clone(),
            f_fn,
            false,
            false,
            batch_size,
        ) {
            map_queries.push(PartQueries::Semantic(p));
        }

        let programs = MultiDimProgramQueries::new(map_queries);

        MapPrograms::new(
            MapProgramQueries::MultiQuery(programs),
            m_fn.clone(),
            v_fn.clone(),
            t_fn.clone(),
            f_fn.clone(),
            false,
        )
    }
}


// pub fn get_program_iter_new(    unit: &VelosiAstUnitSegment,
//     batch_size: usize,
//     starting_prog: Option<Program>) -> MapPrograms
// {

// }



pub fn synthesize(
    z3: &mut Z3WorkerPool,
    unit: &VelosiAstUnitSegment,
    starting_prog: Option<Program>,
) -> Result<Program, VelosiSynthIssues> {
    let batch_size = std::cmp::max(DEFAULT_BATCH_SIZE, z3.num_workers());
    let mut progs = get_program_iter(unit, batch_size, starting_prog);
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
    Err(VelosiSynthIssues::new())
}
