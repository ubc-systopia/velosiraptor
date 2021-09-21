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

//! Code Generation Module

// the used external libraries
use custom_error::custom_error;
use std::path::Path;

// the code generation backends
mod c;
mod rust;

// used library internal modules
use crate::ast::Ast;
use crate::codegen::c::BackendC;
use crate::codegen::rust::BackendRust;

const COPYRIGHT: &str = "2021 Systopia Lab, Computer Science, University of British Columbia";

// custom error definitions
custom_error! {#[derive(PartialEq)] pub CodeGenError
    IOError           = "The input file could not be read.",
    FmtError          = "Could not format in buffer"
}

impl std::convert::From<std::io::Error> for CodeGenError {
    fn from(_other: std::io::Error) -> CodeGenError {
        CodeGenError::IOError
    }
}

pub enum CodeGen {
    Rust(BackendRust),
    C(BackendC),
}

impl CodeGen {
    pub fn new_rust(outdir: &Path, pkg: String) -> CodeGen {
        CodeGen::Rust(BackendRust::new(pkg, outdir))
    }

    pub fn new_c(outdir: &Path, pkg: String) -> CodeGen {
        CodeGen::C(BackendC::new(pkg, outdir))
    }

    pub fn prepare(&self) -> Result<(), CodeGenError> {
        match self {
            CodeGen::Rust(b) => b.prepare(),
            CodeGen::C(b) => b.prepare(),
        }
    }

    pub fn generate_globals(&self, ast: &Ast) -> Result<(), CodeGenError> {
        match self {
            CodeGen::Rust(b) => b.generate_globals(ast),
            CodeGen::C(b) => b.generate_globals(ast),
        }
    }

    pub fn generate_interface(&self, ast: &Ast) -> Result<(), CodeGenError> {
        match self {
            CodeGen::Rust(b) => b.generate_interfaces(ast),
            CodeGen::C(b) => b.generate_interfaces(ast),
        }
    }

    pub fn generate_units(&self, ast: &Ast) -> Result<(), CodeGenError> {
        match self {
            CodeGen::Rust(b) => b.generate_units(ast),
            CodeGen::C(b) => b.generate_units(ast),
        }
    }

    pub fn finalize(&self, ast: &Ast) -> Result<(), CodeGenError> {
        match self {
            CodeGen::Rust(b) => b.finalize(ast),
            CodeGen::C(b) => b.finalize(ast),
        }
    }
}

pub trait CodeGenBackend {
    fn prepare(&self) -> Result<(), CodeGenError>;
    fn generate_globals(&self, ast: &Ast) -> Result<(), CodeGenError>;
    fn generate_interfaces(&self, ast: &Ast) -> Result<(), CodeGenError>;
    fn generate_units(&self, ast: &Ast) -> Result<(), CodeGenError>;
    fn finalize(&self, ast: &Ast) -> Result<(), CodeGenError>;
}
