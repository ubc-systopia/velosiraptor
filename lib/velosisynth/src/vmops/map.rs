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

use velosiast::ast::VelosiAstUnitSegment;

use crate::programs::MultiDimIterator;
use crate::{programs::Program, z3::Z3WorkerPool, VelosiSynthIssues};

use super::{
    precond, semantics, utils, CandidateBlockQueries, CandidateFragmentsQueries, CandidateProgram,
    CandidatePrograms,
};

pub fn submit_fragment_queries(
    z3: &mut Z3WorkerPool,
    unit: &VelosiAstUnitSegment,
) -> Result<CandidateFragmentsQueries, VelosiSynthIssues> {
    log::info!(
        target : "[synth::map]",
        "starting synthesizing the map operation"
    );

    // obtain the functions for the map operation
    let m_fn = unit.get_method("map").unwrap();
    let t_fn = unit.get_method("translate").unwrap();
    let f_fn = unit.get_method("matchflags").unwrap();

    //     let t_start = Instant::now();
    //     let now = Instant::now();
    //     let diff = now.saturating_duration_since(t_start);
    //     println!("map: precond satisfy, {:7}, us  ", diff.as_micros());

    // ---------------------------------------------------------------------------------------------
    // Translate: Add a query for each of the pre-conditions of the function
    // ---------------------------------------------------------------------------------------------

    let translate_preconds = precond::submit_method_precond_queries(z3, unit, m_fn, t_fn, false);
    let translate_semantics = semantics::submit_method_semantic_queries(z3, unit, m_fn, t_fn);

    // ---------------------------------------------------------------------------------------------
    // Matchflags: Add a query for each of the pre-conditions of the function
    // ---------------------------------------------------------------------------------------------

    let matchflags_preconds = precond::submit_method_precond_queries(z3, unit, m_fn, f_fn, false);
    let matchflags_semantics = semantics::submit_method_semantic_queries(z3, unit, m_fn, f_fn);

    let queries = CandidateFragmentsQueries {
        translate_preconds,
        translate_semantics,
        matchflags_preconds,
        matchflags_semantics,
    };

    log::info!(target : "[synth::map]", "submitted {} fragment queries", queries.query_count());

    Ok(queries)
}

/// obtain the
pub fn process_fragment_queries(
    z3: &mut Z3WorkerPool,
    unit: &VelosiAstUnitSegment,
    queries: CandidateFragmentsQueries,
) -> Result<CandidateBlockQueries, VelosiSynthIssues> {
    log::info!(target : "[synth::map]", "processing fragment query results");

    let translate_preconds = utils::obtain_sat_results_2d(z3, queries.translate_preconds)?;
    let translate_semantics = utils::obtain_sat_results_2d(z3, queries.translate_semantics)?;

    let matchflags_preconds = utils::obtain_sat_results_2d(z3, queries.matchflags_preconds)?;
    let matchflags_semantics = utils::obtain_sat_results_2d(z3, queries.matchflags_semantics)?;

    // obtain the functions for the map operation
    let m_fn = unit.get_method("map").unwrap();
    let t_fn = unit.get_method("translate").unwrap();
    let f_fn = unit.get_method("matchflags").unwrap();

    let translate_preconds =
        precond::combine_precond_results_submit_queries(z3, m_fn, t_fn, false, translate_preconds);
    let translate_semantics =
        semantics::combine_semantic_results_submit_queries(z3, m_fn, t_fn, translate_semantics);
    let matchflags_preconds =
        precond::combine_precond_results_submit_queries(z3, m_fn, f_fn, false, matchflags_preconds);
    let matchflags_semantics =
        semantics::combine_semantic_results_submit_queries(z3, m_fn, f_fn, matchflags_semantics);

    log::info!(target : "[synth::map]", "submitted {} block queries",
        translate_preconds.len() + translate_semantics.len() + matchflags_preconds.len() + matchflags_semantics.len());
    log::debug!(target : "[synth::map]", " - translate-precond: {}", translate_preconds.len());
    log::debug!(target : "[synth::map]", " - translate-semantics: {}", translate_semantics.len());
    log::debug!(target : "[synth::map]", " - matchflags-precond: {}", matchflags_preconds.len());
    log::debug!(target : "[synth::map]", " - matchflags-semantics: {}", matchflags_semantics.len());

    Ok(CandidateBlockQueries {
        translate_preconds,
        translate_semantics,
        matchflags_preconds,
        matchflags_semantics,
    })
}

pub fn process_block_queries(
    z3: &mut Z3WorkerPool,
    unit: &VelosiAstUnitSegment,
    queries: CandidateBlockQueries,
) -> Result<CandidatePrograms, VelosiSynthIssues> {
    log::info!(target : "[synth::map]", "processing block query results");

    let translate_preconds = utils::maybe_obtain_sat_results(z3, queries.translate_preconds)?;
    let translate_semantics = utils::maybe_obtain_sat_results(z3, queries.translate_semantics)?;

    let matchflags_preconds = utils::maybe_obtain_sat_results(z3, queries.matchflags_preconds)?;
    let matchflags_semantics = utils::maybe_obtain_sat_results(z3, queries.matchflags_semantics)?;

    log::info!(target : "[synth::map]", "total satisfied block queries: {}",
    translate_preconds.len() + translate_semantics.len() + matchflags_preconds.len() + matchflags_semantics.len());
    log::debug!(target : "[synth::map]", " - translate-precond: {}", translate_preconds.len());
    log::debug!(target : "[synth::map]", " - translate-semantics: {}", translate_semantics.len());
    log::debug!(target : "[synth::map]", " - matchflags-precond: {}", matchflags_preconds.len());
    log::debug!(target : "[synth::map]", " - matchflags-semantics: {}", matchflags_semantics.len());

    // obtain the functions for the map operation
    let m_fn = unit.get_method("map").unwrap();
    let t_fn = unit.get_method("translate").unwrap();
    let f_fn = unit.get_method("matchflags").unwrap();

    // combine the results

    let blocks = [
        translate_preconds,
        translate_semantics,
        matchflags_preconds,
        matchflags_semantics,
    ];

    let mut it = MultiDimIterator::from_slice(&blocks);

    let mut res = Vec::with_capacity(it.len());
    while let Some(conf) = it.next() {
        let prog = conf
            .iter()
            .enumerate()
            .fold(Program::new(), |prog, (i, e)| {
                let p = blocks[i][*e]
                    .query()
                    .program()
                    .expect("program was not set.");
                prog.merge(p)
            });

        let translate_preconds =
            precond::submit_program_query(z3, m_fn, t_fn, None, false, prog.clone());
        let translate_semantics =
            semantics::submit_program_query(z3, m_fn, t_fn, None, prog.clone());

        let matchflags_preconds =
            precond::submit_program_query(z3, m_fn, f_fn, None, false, prog.clone());
        let matchflags_semantics = semantics::submit_program_query(z3, m_fn, f_fn, None, prog);

        res.push(CandidateProgram {
            translate_preconds,
            translate_semantics,
            matchflags_preconds,
            matchflags_semantics,
        });
    }

    log::info!(target : "[synth::map]", "submitted {} candidate program queries", res.len());

    Ok(CandidatePrograms(res))
}

pub fn process_program_queries(
    z3: &mut Z3WorkerPool,
    queries: CandidatePrograms,
) -> Result<Program, VelosiSynthIssues> {
    log::info!(target : "[synth::map]", "processing program query results");

    let mut programs = Vec::new();
    for candidate in queries.0 {
        let translate_preconds = utils::obtain_sat_result(z3, candidate.translate_preconds);
        match translate_preconds {
            Ok(Some(_)) => (),
            Ok(None) => {
                // todo: mark other tickets as invalid
                continue;
            }
            Err(e) => return Err(e),
        }

        let translate_semantics = utils::obtain_sat_result(z3, candidate.translate_semantics);
        match translate_semantics {
            Ok(Some(_)) => (),
            Ok(None) => {
                // todo: mark other tickets as invalid
                continue;
            }
            Err(e) => return Err(e),
        }

        let matchflags_preconds = utils::obtain_sat_result(z3, candidate.matchflags_preconds);
        match matchflags_preconds {
            Ok(Some(_)) => (),
            Ok(None) => {
                // todo: mark other tickets as invalid
                continue;
            }
            Err(e) => return Err(e),
        }

        let matchflags_semantics = utils::obtain_sat_result(z3, candidate.matchflags_semantics);
        match matchflags_semantics {
            Ok(Some(mut r)) => {
                let p = r.query_mut().take_program().unwrap();
                programs.push(p);
            }
            Ok(None) => {
                // todo: mark other tickets as invalid
                continue;
            }
            Err(e) => return Err(e),
        };
    }

    if programs.is_empty() {
        log::error!(target : "[synth::map]", "no program satisfying all queries found!");
        panic!("no program found!");
    }

    log::info!(target : "[synth::map]", "found {} programs satisfying all queries", programs.len());

    for (i, p) in programs.iter().enumerate() {
        println!("Program {}: {:?}", i, p);
    }
    Ok(programs.pop().unwrap())
}

pub fn synthesize(
    z3: &mut Z3WorkerPool,
    unit: &VelosiAstUnitSegment,
) -> Result<Program, VelosiSynthIssues> {
    let queries = submit_fragment_queries(z3, unit)?;
    let queries = process_fragment_queries(z3, unit, queries)?;
    let queries = process_block_queries(z3, unit, queries)?;
    process_program_queries(z3, queries)
}

// fn add_synth_map_tasks(&mut self, unit: &mut Segment) -> Vec<Vec<Vec<Z3Ticket>>> {

//     let now = Instant::now();
//     let diff = now.saturating_duration_since(t_start);
//     println!("map: tfn precond, {:7}, us  ", diff.as_micros());

// fn check_synth_map_tasks(&mut self, unit: &mut Segment, mut tickets: Vec<Vec<Vec<Z3Ticket>>>) {
//     // get the map functions
//     let m_fn = unit.get_method("map").unwrap();
//     // get the translate function
//     let t_fn = unit.get_method("translate").unwrap();
//     // get the translate function
//     let f_fn = unit.get_method("matchflags").unwrap();

//     let results = Arc::new(
//         tickets
//             .drain(..)
//             .flat_map(|t| self.obtain_sat_results(t))
//             .collect::<Vec<_>>(),
//     );

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
//         let mut p_tickets =
//             self.check_programs_precond(m_fn, f_fn, None, false, vec![prog.clone()]);
//         p_tickets.extend(self.check_programs_precond(
//             m_fn,
//             t_fn,
//             None,
//             false,
//             vec![prog.clone()],
//         ));
//         p_tickets.extend(self.check_programs_translate(m_fn, t_fn, vec![prog.clone()]));
//         p_tickets.extend(self.check_programs_matchflags(m_fn, f_fn, vec![prog.clone()]));

//         let mut all_sat = true;
//         for t in p_tickets {
//             let res = self.workerpool.wait_for_result(t);
//             let mut reslines = res.result().lines();
//             all_sat &= reslines.next() == Some("sat");
//         }

//         if all_sat {
//             println!("found candidate program: {:?}", prog);
//             unit.map_ops = Some(prog.into());
//             return;
//         }
//     }
//     println!("no candidate program found");
// }
