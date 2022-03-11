// Velosiraptor Compiler
//
//
// MIT License
//
// Copyright (c) 2022 The University of British Columbia, Vancouver, BC, Canada
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

//! # The Hardware Generator Module
//!
//! This module contains different backends to generate hardware components
//! corresponding to the velosiraptor specifications.

// the used external libraries
use custom_error::custom_error;
use std::path::Path;

// the hardware backends
mod fastmodels;

// the used library modules
use crate::ast::AstRoot;
use crate::hwgen::fastmodels::ArmFastModelsModule;

// copy right notice for the generated files
const COPYRIGHT: &str =
    "Copyright (c) 2022 The University of British Columbia, Vancouver, BC, Canada";

// custom error definitions for the hardware generation
custom_error! {#[derive(PartialEq)] pub HWGenError
    IOError           = "The input file could not be read.",
    FmtError          = "Could not format in buffer"
}

impl std::convert::From<std::io::Error> for HWGenError {
    fn from(_other: std::io::Error) -> HWGenError {
        HWGenError::IOError
    }
}

/// the hardware generator context
pub enum HWGen {
    FastModels(ArmFastModelsModule),
}

impl HWGen {
    /// creates a new generator for the Arm FastModels platform
    pub fn new_fastmodels(outdir: &Path, pkg: String) -> HWGen {
        let path = outdir.join(pkg.as_str()).join("hw");
        HWGen::FastModels(ArmFastModelsModule::new(path.as_path(), pkg))
    }

    pub fn prepare(&self) -> Result<(), HWGenError> {
        match self {
            HWGen::FastModels(b) => b.prepare(),
        }
    }

    pub fn generate(&self, ast: &AstRoot) -> Result<(), HWGenError> {
        match self {
            HWGen::FastModels(b) => {
                b.generate_unit(ast)?;
                b.generate_interface(ast)?;
                b.generate_state(ast)
            }
        }
    }

    pub fn finalize(&self) -> Result<(), HWGenError> {
        match self {
            HWGen::FastModels(b) => b.finalize(),
        }
    }
}

pub trait HWGenBackend {
    /// prepares the component generation, creating the directories etc
    fn prepare(&self) -> Result<(), HWGenError>;

    /// generates the unit
    fn generate_unit(&self, ast: &AstRoot) -> Result<(), HWGenError>;

    /// generate the interface definitions
    fn generate_interface(&self, ast: &AstRoot) -> Result<(), HWGenError>;

    /// generates the state representation
    fn generate_state(&self, ast: &AstRoot) -> Result<(), HWGenError>;

    /// finalizes the code generation part
    fn finalize(&self) -> Result<(), HWGenError>;
}
