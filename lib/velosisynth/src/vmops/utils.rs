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

use crate::{Program, ProgramsBuilder};

use super::resultparser;

pub fn make_program_builder(
    unit: &VelosiAstUnitSegment,
    m_goal: &VelosiAstMethod,
    pre: &VelosiAstExpr,
) -> ProgramsBuilder {
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
            .field(fieldname)
            .expect("didn't find the field");
        if let Some(slicename) = parts.next() {
            let slice = field.slice(slicename).expect("didn't find the slice");
            builder.add_field_slice(fieldname, slicename, slice.nbits() as usize);
        } else {
            builder.add_field(fieldname.to_string());
        }
    }

    builder
}

#[derive(PartialEq, Eq)]
pub enum QueryResult {
    Sat,
    Unsat,
    Unknown,
    Error,
}

pub fn check_result_no_rewrite(output: &str) -> QueryResult {
    let mut reslines = output.lines();
    match reslines.next() {
        Some("sat") => QueryResult::Sat,
        Some("unsat") => QueryResult::Unsat,
        Some(_a) => QueryResult::Error,
        None => {
            unreachable!("unexpected none output")
        }
    }
}

pub fn check_result(output: &str, program: &mut Program) -> QueryResult {
    let mut reslines = output.lines();
    match reslines.next() {
        Some("sat") => {
            log::debug!(target: "[CheckResult]", " - sat: {:?}", program);
            if reslines.next().is_some() {
                match resultparser::parse_result(&output[4..]) {
                    Ok(mut vars) => {
                        if !vars.is_empty() {
                            program.replace_symbolic_values(&mut vars);
                        }
                    }
                    Err(_e) => (),
                }
            }
            QueryResult::Sat
        }
        Some("unsat") => {
            log::trace!(target: "[CheckResult]", " - unsat: {:?}", program);
            QueryResult::Unsat
        }
        Some("unknown") => {
            log::trace!(target: "[CheckResult]", " - unknown: {:?}", program);
            QueryResult::Unknown
        }
        Some(a) => {
            log::error!(target: "[CheckResult]", " - {} {:?}", a, program);
            if a.starts_with("(error") {
                QueryResult::Error
            } else {
                unreachable!("unexpected none output: {}", a);
            }
        }
        None => {
            unreachable!("unexpected none output")
        }
    }
}
