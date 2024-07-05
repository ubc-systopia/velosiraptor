// VelosiSynth -- a synthesizer for the Velosiraptor
//
//
// MIT License
//
// Copyright (c) 2024 Systopia Lab, Computer Science, University of British Columbia
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

//! # SynthOpts -- Synthesis Options

/// the default batch size for submitting the queries to the solver
pub const DEFAULT_BATCH_SIZE: usize = 5;

/// Options for controlling synthesis
#[derive(Debug, Clone)]
pub struct SynthOpts {
    pub batch_size: usize,
    pub enable_mem_model: bool,
    pub disable_state_opt: bool,
    pub disable_iface_opt: bool,
    pub disable_expr_opt: bool,
    pub disable_tree_opt: bool,
    pub disable_cache_opt: bool,
    pub disable_program_generation: bool,
}

impl SynthOpts {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_batchsize(batch_size: usize) -> Self {
        Self {
            batch_size,
            ..Self::default()
        }
    }
}

impl Default for SynthOpts {
    fn default() -> Self {
        Self {
            batch_size: DEFAULT_BATCH_SIZE,
            enable_mem_model: false,
            disable_iface_opt: false,
            disable_state_opt: false,
            disable_expr_opt: false,
            disable_tree_opt: false,
            disable_cache_opt: false,
            disable_program_generation: false,
        }
    }
}
