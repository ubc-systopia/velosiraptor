// VelosiSynth - A synthesizer for Translation Software
//
//
// MIT License
//
// Copyright (c) 2021 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiSynth -- Z3 bindings for Synthesis
//!
//! This module provides interfaces to deal with Z3 Based synthesis

#[cfg(all(feature = "z3-library", feature = "z3-standalone"))]
compile_error!("Can't enable features `z3-library` and `z3-standalone` at the same time");

#[cfg(feature = "z3-library")]
mod instance_library;
#[cfg(feature = "z3-standalone")]
mod instance_standalone;

mod query;
mod taskq;
mod worker;

// public re-exports
#[cfg(feature = "z3-library")]
pub use instance_library::Z3Instance;
#[cfg(feature = "z3-standalone")]
pub use instance_standalone::Z3Instance;

pub use query::{Z3Query, Z3Result, Z3Ticket};
use taskq::TaskQ;
pub use taskq::Z3TaskPriority;
pub use worker::{Z3Worker, Z3WorkerPool, Z3WorkerPoolStats};

/// Errors reported by Z3
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Z3Error {
    #[cfg(feature = "z3-standalone")]
    QueryExecution,
}
