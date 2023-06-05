// VelosiHwGen -- A hardware generator for the Velosiraptor language
//
//
// MIT License
//
// Copyright (c) 2022, 2023 Systopia Lab, Computer Science, University of British Columbia
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

use std::path::Path;

// the hardware backends
mod fastmodels;

const COPYRIGHT: &str =
    "2022 Systopia Lab, Computer Science, University of British Columbia.\nAll rights reserved.";

#[derive(Debug)]
pub enum VelosiHwGenError {
    IoError(std::io::Error),
}

impl From<std::io::Error> for VelosiHwGenError {
    fn from(err: std::io::Error) -> Self {
        VelosiHwGenError::IoError(err)
    }
}

use velosiast::VelosiAst;
use crate::fastmodels::ArmFastModelsModule;

/// the hardware generator context
pub enum VelosiHwGen {
    FastModels(ArmFastModelsModule),
}

impl VelosiHwGen {
    /// creates a new generator for the Arm FastModels platform
    pub fn new_fastmodels(outdir: &Path, pkg: String) -> VelosiHwGen {
        let path = outdir.join(pkg.as_str()).join("hw");
        VelosiHwGen::FastModels(ArmFastModelsModule::new(path.as_path(), pkg))
    }

    pub fn prepare(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError> {
        match self {
            VelosiHwGen::FastModels(b) => b.prepare(ast),
        }
    }

    pub fn generate(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError> {
        match self {
            VelosiHwGen::FastModels(b) => {
                b.generate_interfaces(ast)?;
                b.generate_states(ast)?;
                b.generate_units(ast)
            }
        }
    }

    pub fn finalize(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError> {
        match self {
            VelosiHwGen::FastModels(b) => b.finalize(ast),
        }
    }
}

pub trait VelosiHwGenBackend {
    /// prepares the component generation, creating the directories etc
    fn prepare(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError>;

    /// generates the unit
    fn generate_units(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError>;

    /// generate the interface definitions
    fn generate_interfaces(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError>;

    /// generates the state representation
    fn generate_states(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError>;

    /// finalizes the code generation part
    fn finalize(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError>;
}
