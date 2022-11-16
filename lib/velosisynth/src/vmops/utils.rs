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

use std::collections::HashSet;
use std::sync::Arc;

use velosiast::ast::{VelosiAstExpr, VelosiAstMethod, VelosiAstUnitSegment};

use crate::vmops::TicketOrResult;
use crate::z3::{Z3Result, Z3Ticket, Z3WorkerPool};
use crate::VelosiSynthIssues;
use crate::{Program, ProgramsBuilder};

use super::resultparser;

pub fn construct_programs(
    unit: &VelosiAstUnitSegment,
    m_goal: &VelosiAstMethod,
    pre: &VelosiAstExpr,
) -> Vec<Program> {
    log::info!(target: "[vmops::utils]", "constructing programs;");
    // obtain the state references in the pre-condition
    let mut state_syms = HashSet::new();
    pre.get_state_references(&mut state_syms);

    // obtain the state bits that are referenced in the pre-condition
    let state_bits = unit.state.get_field_slice_refs(&state_syms);

    // finally obtain the fields that matter using back-projection
    let st_access_fields = unit
        .interface
        .fields_accessing_state(&state_syms, &state_bits);

    // construct the program builder
    let mut builder = ProgramsBuilder::new();

    // add the variables that the function talks about
    for v in m_goal.params.iter() {
        // flags show up differently
        if v.ptype.is_flags() {
            if let Some(flags) = &unit.flags {
                let var = Arc::new(v.ident_to_string());
                for f in flags.flags.iter() {
                    builder.add_flags(var.clone(), f.to_string());
                }
            } else {
                unreachable!("shoudl have defined flags!");
            }
        } else {
            builder.add_var(v.ident_to_string());
        }
    }

    // add the fields to the program builder
    for f in st_access_fields.iter() {
        let mut parts = f.split('.');
        let _ = parts.next();
        let fieldname = parts.next().unwrap();

        let field = unit
            .interface
            .field(&fieldname)
            .expect("didn't find the field");
        if let Some(slicename) = parts.next() {
            let slice = field.slice(slicename).expect("didn't find the slice");
            builder.add_field_slice(fieldname, slicename, slice.bits());
        } else {
            unimplemented!("not yet implementation");
            //builder.add_field(field);
        }
    }

    // build the programs
    builder.construct_new_programs()
}

pub fn obtain_sat_results_2d(
    z3: &mut Z3WorkerPool,
    fn_tickets: Vec<Vec<Z3Ticket>>,
) -> Result<Vec<Vec<Z3Result>>, VelosiSynthIssues> {
    let mut fn_results = Vec::with_capacity(fn_tickets.len());
    for tickets in fn_tickets.into_iter() {
        let results = obtain_sat_results(z3, tickets)?;
        fn_results.push(results);
    }
    Ok(fn_results)
}

pub fn obtain_sat_result(
    z3: &mut Z3WorkerPool,
    ticket: Z3Ticket,
) -> Result<Option<Z3Result>, VelosiSynthIssues> {
    let mut res = z3.wait_for_result(ticket);

    // res.print_timestamps();
    let output = res.result();

    let mut reslines = output.lines();
    match reslines.next() {
        Some("sat") => {
            log::debug!(target: "[ObtainResult]", " - sat: {:?}", res.query().program());
            if reslines.next().is_some() {
                match resultparser::parse_result(&output[4..]) {
                    Ok(mut vars) => {
                        if !vars.is_empty() {
                            // println!("rewriting the program: {:?}\n", vars);
                            res.query_mut()
                                .program_mut()
                                .replace_symbolic_values(&mut vars);
                        }
                    }
                    Err(_e) => (),
                }
            }
            Ok(Some(res))
        }
        Some("unsat") => {
            log::trace!(target: "[ObtainResult]", " - unsat: {:?}", res.query().program());
            Ok(None)
        }
        Some(a) => {
            log::error!(target: "[ObtainResult]", " - {} {:?}", a, res.query().program());
            if a.starts_with("(error") {
                panic!("!handle me: {}", a);
            } else {
                unreachable!("unexpected none output: {}", a);
            }
        }
        None => {
            unreachable!("unexpected none output")
        }
    }
}

pub fn obtain_sat_results(
    z3: &mut Z3WorkerPool,
    fn_tickets: Vec<Z3Ticket>,
) -> Result<Vec<Z3Result>, VelosiSynthIssues> {
    let mut results = Vec::new();
    for t in fn_tickets {
        let res = obtain_sat_result(z3, t)?;
        if let Some(res) = res {
            results.push(res);
        }
    }
    Ok(results)
}

pub fn maybe_obtain_sat_results(
    z3: &mut Z3WorkerPool,
    mut fn_tickets: TicketOrResult,
) -> Result<Vec<Z3Result>, VelosiSynthIssues> {
    match fn_tickets {
        TicketOrResult::Ticket(tickets) => obtain_sat_results(z3, tickets),
        TicketOrResult::Result(results) => Ok(results),
    }
}
