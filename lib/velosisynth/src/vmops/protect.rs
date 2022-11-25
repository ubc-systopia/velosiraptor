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

pub struct ProtectPrograms {
    programs: MultiDimProgramQueries<PartQueries>,
    programs_done: bool,
    queries: LinkedList<(Program, [Option<Z3Ticket>; 2])>,
    candidates: Vec<Program>,

    m_fn: Rc<VelosiAstMethod>,
    t_fn: Rc<VelosiAstMethod>,
    f_fn: Rc<VelosiAstMethod>,
}

impl ProtectPrograms {
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
                // let translate_preconds = precond::submit_program_query(
                //     z3,
                //     self.m_fn.as_ref(),
                //     self.t_fn.as_ref(),
                //     None,
                //     false,
                //     prog.clone(),
                // );

                let translate_semantics = semantics::submit_program_query(
                    z3,
                    self.m_fn.as_ref(),
                    self.t_fn.as_ref(),
                    None,
                    prog.clone(),
                    true,
                );

                // let matchflags_preconds = precond::submit_program_query(
                //     z3,
                //     self.m_fn.as_ref(),
                //     self.f_fn.as_ref(),
                //     None,
                //     false,
                //     prog.clone(),
                // );
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
                        // Some(translate_preconds),
                        Some(translate_semantics),
                        // Some(matchflags_preconds),
                        Some(matchflags_semantics),
                    ],
                ));
            }
        }

        let mut res_program = None;
        let mut remaining_queries = LinkedList::new();
        while let Some((prog, mut tickets)) = self.queries.pop_front() {
            let mut all_done = true;
            let mut unsat_part = false;
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

    let map_queries = vec![
        // PartQueries::Precond(precond::precond_query(
        //     unit,
        //     m_fn.clone(),
        //     t_fn.clone(),
        //     false,
        // )),
        // PartQueries::Precond(precond::precond_query(
        //     unit,
        //     m_fn.clone(),
        //     f_fn.clone(),
        //     false,
        // )),
        PartQueries::Semantic(semantics::semantic_query(
            unit,
            m_fn.clone(),
            t_fn.clone(),
            true,
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

    ProtectPrograms::new(programs, m_fn.clone(), t_fn.clone(), f_fn.clone())
}

pub fn synthesize(
    z3: &mut Z3WorkerPool,
    unit: &VelosiAstUnitSegment,
) -> Result<Program, VelosiSynthIssues> {
    let batch_size = std::cmp::max(5, z3.num_workers() / 2);
    let mprogs = get_program_iter(unit, batch_size);
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

// fn add_synth_protect_tasks(&mut self, unit: &mut Segment) -> Vec<Vec<Vec<Z3Ticket>>> {
//     // get the map functions
//     let p_fn = unit.get_method("protect").unwrap();
//     // get the translate function
//     let t_fn = unit.get_method("translate").unwrap();
//     // get the translate function
//     let f_fn = unit.get_method("matchflags").unwrap();

//     // --------------------------------------------------------------------------------------
//     // Check whether the pre-conditions can be satisfied
//     // --------------------------------------------------------------------------------------

//     // --------------------------------------------------------------------------------------
//     // Matchflags: check the expression result
//     // --------------------------------------------------------------------------------------
//     // TODO: that on here might be memoised...

//     let mf_res_tickets = {
//         let state_syms = f_fn.get_state_references_body();
//         let state_bits = unit.state.referenced_field_bits(&state_syms);
//         let st_access_fields = unit
//             .interface
//             .fields_accessing_state(&state_syms, &state_bits);

//         // construct the program builder
//         let mut builder = operations::ProgramsBuilder::new();
//         for v in f_fn.args.iter() {
//             if v.ptype == Type::Flags {
//                 if let Some(flags) = &unit.flags {
//                     let var = Arc::new(v.name.clone());
//                     for f in flags.flags.iter() {
//                         builder.add_flags(var.clone(), f.name.clone());
//                     }
//                 }
//             } else {
//                 builder.add_var(v.name.clone());
//             }
//         }

//         for f in st_access_fields.iter() {
//             let mut parts = f.split('.');
//             let _ = parts.next();
//             let field = parts.next().unwrap();
//             let slice = parts.next().unwrap();
//             builder.add_field_slice(field, slice);
//         }

//         let progs = builder.construct_programs(true);
//         self.check_programs_protect(p_fn, f_fn, t_fn, progs)
//     };

//     vec![vec![mf_res_tickets]]

//     // change permissions
//     //   post: matchflags(s') && translate(s') == translate(s)
// }

// fn check_synth_protect_tasks(
//     &mut self,
//     unit: &mut Segment,
//     mut tickets: Vec<Vec<Vec<Z3Ticket>>>,
// ) {
//     // get the map functions
//     let p_fn = unit.get_method("protect").unwrap();
//     // get the translate function
//     let t_fn = unit.get_method("translate").unwrap();
//     // get the translate function
//     let f_fn = unit.get_method("matchflags").unwrap();

//     let results = tickets
//         .drain(..)
//         .flat_map(|t| self.obtain_sat_results(t))
//         .collect::<Vec<_>>();

//     // the completed candidate program
//     let mut candidate_programs: Vec<Vec<&Program>> = vec![Vec::new()];

//     for res in results.iter() {
//         // new candidate programs
//         let mut new_candidate_programs = Vec::new();

//         for prog in candidate_programs {
//             for r in res {
//                 // expand all candidate programs with the new program
//                 let mut new_prog = prog.clone();
//                 new_prog.push(r.query().program().unwrap());
//                 new_candidate_programs.push(new_prog);
//             }
//         }

//         // update the candidate programs
//         candidate_programs = new_candidate_programs;
//     }

//     let mut candidate_programs: Vec<Program> = candidate_programs
//         .iter_mut()
//         .map(|p| p.iter_mut().fold(Program::new(), |acc, x| acc.merge(x)))
//         .collect();

//     for prog in candidate_programs.drain(..) {
//         println!("checking: {:?}", prog);

//         let p_tickets = self.check_programs_protect(p_fn, f_fn, t_fn, vec![prog.clone()]);

//         let mut all_sat = true;
//         for t in p_tickets {
//             let res = self.workerpool.wait_for_result(t);
//             let mut reslines = res.result().lines();
//             all_sat &= reslines.next() == Some("sat");
//         }
//         if all_sat {
//             println!("found candidate program: {:?}", prog);
//             unit.protect_ops = Some(prog.into());
//             return;
//         }
//     }
//     println!("no candidate program found");
// }
