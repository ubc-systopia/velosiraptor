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

use std::fmt::{Display, Formatter, Result as FmtResult};

pub mod map;
mod precond;
pub mod protect;
mod resultparser;
pub mod sanity;
mod semantics;
pub mod unmap;
mod utils;

use crate::z3::{Z3Result, Z3Ticket};

/// a combined program
pub enum TicketOrResult {
    Ticket(Vec<Z3Ticket>),
    Result(Vec<Z3Result>),
}

impl TicketOrResult {
    pub fn len(&self) -> usize {
        match self {
            TicketOrResult::Ticket(tickets) => tickets.len(),
            TicketOrResult::Result(results) => results.len(),
        }
    }
}

pub struct CandidateFragmentsQueries {
    translate_preconds: Vec<Vec<Z3Ticket>>,
    translate_semantics: Vec<Vec<Z3Ticket>>,
    matchflags_preconds: Vec<Vec<Z3Ticket>>,
    matchflags_semantics: Vec<Vec<Z3Ticket>>,
}

impl CandidateFragmentsQueries {
    pub fn query_count(&self) -> usize {
        self.translate_preconds
            .iter()
            .fold(0, |acc, x| acc + x.len())
            + self
                .translate_semantics
                .iter()
                .fold(0, |acc, x| acc + x.len())
            + self
                .matchflags_preconds
                .iter()
                .fold(0, |acc, x| acc + x.len())
            + self
                .matchflags_semantics
                .iter()
                .fold(0, |acc, x| acc + x.len())
    }
}

impl Display for CandidateFragmentsQueries {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, " - translate-precond: ")?;
        for a in self.translate_preconds.iter() {
            write!(f, "{:?}, ", a.len())?;
        }
        write!(f, "\n - translate-semantics: ")?;
        for a in self.translate_semantics.iter() {
            write!(f, "{:?}, ", a.len())?;
        }
        write!(f, "\n - matchflags-precond: ")?;
        for a in self.matchflags_preconds.iter() {
            write!(f, "{:?}, ", a.len())?;
        }
        write!(f, "\n - matchflags-semantics: ")?;
        for a in self.matchflags_semantics.iter() {
            write!(f, "{:?}, ", a.len())?;
        }
        Ok(())
    }
}

pub struct CandidateBlockQueries {
    translate_preconds: TicketOrResult,
    translate_semantics: TicketOrResult,
    matchflags_preconds: TicketOrResult,
    matchflags_semantics: TicketOrResult,
}

struct CandidateProgram {
    translate_preconds: Z3Ticket,
    translate_semantics: Z3Ticket,
    matchflags_preconds: Z3Ticket,
    matchflags_semantics: Z3Ticket,
}

// the candidate programs
pub struct CandidatePrograms(Vec<CandidateProgram>);
