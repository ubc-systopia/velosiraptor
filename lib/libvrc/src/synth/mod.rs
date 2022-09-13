// Velosiraptor Code Generator
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

//! Synthesis Module

// the used external libraries
use custom_error::custom_error;
use std::path::Path;

// the code generation backends
mod operation;
mod rosette;
mod z3;

// the used library modules
use crate::ast::AstRoot;
pub use crate::synth::operation::{OpExpr, Operation};
use crate::synth::rosette::SynthRosette;
use crate::synth::z3::SynthZ3;

const COPYRIGHT: &str = "2021 Systopia Lab, Computer Science, University of British Columbia";

// custom error definitions
custom_error! {#[derive(PartialEq, Eq)] pub SynthError
    IOError           = "The output file could not be written",
    SynthError        = "The synthesizer returned an error",
    FmtError          = "Could not format in buffer"
}

impl std::convert::From<std::io::Error> for SynthError {
    fn from(_other: std::io::Error) -> SynthError {
        SynthError::IOError
    }
}

/// the
pub enum Synthesisizer {
    Rosette(SynthRosette),
    Z3(SynthZ3),
}

impl Synthesisizer {
    /// creates a new rosette synthesizer
    pub fn new_rosette(outdir: &Path, pkg: String) -> Synthesisizer {
        Synthesisizer::Rosette(SynthRosette::new(outdir, pkg))
    }

    pub fn new_z3(outdir: &Path, pkg: String, parallelism: usize) -> Synthesisizer {
        Synthesisizer::Z3(SynthZ3::new(outdir, pkg, parallelism))
    }

    /// synthesizes the `map` function and returns an ast of it
    pub fn synth_map(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
        use Synthesisizer::*;
        match self {
            Rosette(r) => r.synth_map(ast),
            Z3(r) => r.synth_map(ast),
        }
    }

    /// synthesizes the 'unmap' function and returns an ast of it
    pub fn synth_unmap(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
        use Synthesisizer::*;
        match self {
            Rosette(r) => r.synth_unmap(ast),
            Z3(r) => r.synth_unmap(ast),
        }
    }

    pub fn synth_protect(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
        use Synthesisizer::*;
        match self {
            Rosette(r) => r.synth_protect(ast),
            Z3(r) => r.synth_protect(ast),
        }
    }

    pub fn synth_map_unmap_protect(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
        use Synthesisizer::*;
        match self {
            Rosette(r) => r.synth_map_unmap_protect(ast),
            Z3(r) => r.synth_map_unmap_protect(ast),
        }
    }
}
