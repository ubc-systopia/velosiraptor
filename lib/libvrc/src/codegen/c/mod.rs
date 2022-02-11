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

//! C Code Generartion Backend

use std::path::Path;

use crate::ast::AstRoot;
use crate::codegen::CodeGenBackend;
use crate::codegen::CodeGenError;

pub struct BackendC {
    //  outdir: PathBuf,
}

impl BackendC {
    pub fn new(_pkg: String, _outdir: &Path) -> Self {
        BackendC {
            // let path = outdir.join("clang");
           // outdir: outdir.to_path_buf(),
        }
    }
}

impl CodeGenBackend for BackendC {
    fn prepare(&self) -> Result<(), CodeGenError> {
        Ok(())
    }
    fn generate_globals(&self, _ast: &AstRoot) -> Result<(), CodeGenError> {
        Ok(())
    }
    fn generate_interfaces(&self, _ast: &AstRoot) -> Result<(), CodeGenError> {
        Ok(())
    }
    fn generate_units(&self, _ast: &AstRoot) -> Result<(), CodeGenError> {
        Ok(())
    }
    fn finalize(&self, _ast: &AstRoot) -> Result<(), CodeGenError> {
        Ok(())
    }
}
