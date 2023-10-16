// VelosiParser -- a parser for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2021, 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiParser -- The Velosiraptor Parser
//!
//! The VelosiParser consumes the lexed TokenStream and produces a parse tree for the
//! for further processing.

// used standard library functionality

use std::path::Path;

// the code generation backends
mod c;
mod rust;

use crate::c::BackendC;
use crate::rust::BackendRust;

use velosiast::VelosiAst;

const COPYRIGHT: &str =
    "2022 Systopia Lab, Computer Science, University of British Columbia. All rights reserved.";

#[derive(Debug)]
pub enum VelosiCodeGenError {
    IoError(std::io::Error),
}

impl From<std::io::Error> for VelosiCodeGenError {
    fn from(err: std::io::Error) -> Self {
        VelosiCodeGenError::IoError(err)
    }
}

/// The Velosiraptor Code Generator
pub enum VelosiCodeGen {
    Rust(BackendRust),
    C(BackendC),
}

impl VelosiCodeGen {
    pub fn new_rust(outdir: &Path, pkg: String) -> VelosiCodeGen {
        let path = outdir.join(pkg.as_str()).join("sw");
        VelosiCodeGen::Rust(BackendRust::new(pkg, path.as_path()))
    }

    pub fn new_c(outdir: &Path, pkg: String) -> VelosiCodeGen {
        let path = outdir.join(pkg.as_str()).join("sw");
        VelosiCodeGen::C(BackendC::new(pkg, path.as_path()))
    }

    pub fn prepare(&self, ast: &VelosiAst, osspec: &VelosiAst) -> Result<(), VelosiCodeGenError> {
        match self {
            VelosiCodeGen::Rust(b) => b.prepare(ast, osspec),
            VelosiCodeGen::C(b) => b.prepare(osspec),
        }
    }

    pub fn generate_globals(
        &self,
        ast: &VelosiAst,
        osspec: &VelosiAst,
    ) -> Result<(), VelosiCodeGenError> {
        match self {
            VelosiCodeGen::Rust(b) => b.generate_globals(ast, osspec),
            VelosiCodeGen::C(b) => b.generate_globals(ast, osspec),
        }
    }

    pub fn generate_interface(
        &self,
        ast: &VelosiAst,
        osspec: &VelosiAst,
    ) -> Result<(), VelosiCodeGenError> {
        match self {
            VelosiCodeGen::Rust(b) => b.generate_interfaces(ast, osspec),
            VelosiCodeGen::C(b) => b.generate_interfaces(ast, osspec),
        }
    }

    pub fn generate_units(
        &self,
        ast: &VelosiAst,
        osspec: &VelosiAst,
    ) -> Result<(), VelosiCodeGenError> {
        match self {
            VelosiCodeGen::Rust(b) => b.generate_units(ast, osspec),
            VelosiCodeGen::C(b) => b.generate_units(ast, osspec),
        }
    }

    pub fn finalize(&self, ast: &VelosiAst, osspec: &VelosiAst) -> Result<(), VelosiCodeGenError> {
        match self {
            VelosiCodeGen::Rust(b) => b.finalize(ast, osspec),
            VelosiCodeGen::C(b) => b.finalize(ast, osspec),
        }
    }

    pub fn generate(&self, ast: &VelosiAst, osspec: &VelosiAst) -> Result<(), VelosiCodeGenError> {
        self.prepare(ast, osspec)?;
        self.generate_globals(ast, osspec)?;
        self.generate_interface(ast, osspec)?;
        self.generate_units(ast, osspec)?;
        self.finalize(ast, osspec)
    }

    pub fn test_compile(&self, ast: &VelosiAst, osspec: &VelosiAst) -> Result<(), String> {
        match self {
            VelosiCodeGen::Rust(b) => b.test_compile(ast, osspec),
            VelosiCodeGen::C(b) => b.test_compile(ast, osspec),
        }
    }
}
