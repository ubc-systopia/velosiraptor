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

//! Synthesis Module: Rosette

// external libraries
use std::fs;
use std::path::{Path, PathBuf};

// the used libraries
use crate::ast::{AstRoot, Method, Type};
use crate::synth::SynthError;
use rosettelang::RosetteFile;

pub struct SynthRosette {
    outdir: PathBuf,
    pkg: String,
}

impl SynthRosette {
    pub fn new(outdir: &Path, pkg: String) -> Self {
        SynthRosette {
            outdir: outdir.join(&pkg).join("synth"),
            pkg,
        }
    }

    /// synthesizes the `map` function and returns an ast of it
    pub fn synth_map(&self, ast: &AstRoot) -> Result<Method, SynthError> {
        fs::create_dir_all(&self.outdir)?;

        for unit in &ast.units {
            println!("synthesizing map: for {} in {:?}", unit.name, self.outdir);
            let rktfilepath = self.outdir.join(format!("{}.rkt", unit.name));
            let doc = format!("Unit: {}, Function: map()", unit.name);

            let mut rkt = RosetteFile::new(rktfilepath, doc);

            rkt.add_new_require(String::from("rosette/lib/syntax"));
            rkt.add_new_require(String::from("rosette/lib/destruct"));

            rkt.save();
            rkt.synth();
        }

        Ok(Method::new(String::from("map"), Type::Boolean, Vec::new()))
    }

    /// synthesizes the 'unmap' function and returns an ast of it
    pub fn synth_unmap(&self, ast: &AstRoot) -> Result<Method, SynthError> {
        for unit in &ast.units {
            println!("synthesizing map: for {} in {:?}", unit.name, self.outdir);
        }

        Ok(Method::new(
            String::from("unmap"),
            Type::Boolean,
            Vec::new(),
        ))
    }

    pub fn synth_protect(&self, ast: &AstRoot) -> Result<Method, SynthError> {
        for unit in &ast.units {
            println!("synthesizing map: for {} in {:?}", unit.name, self.outdir);
        }

        Ok(Method::new(
            String::from("protect"),
            Type::Boolean,
            Vec::new(),
        ))
    }
}
