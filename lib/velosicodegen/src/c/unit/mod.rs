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

//! Unit Generation (C)

use std::path::PathBuf;

mod enums;
mod segment;
mod staticmap;

use velosiast::{VelosiAst, VelosiAstUnit};
use velosicomposition::Relations;

use super::utils;
use crate::VelosiCodeGenError;

/// starts the interface code generation
pub fn generate(
    unit: &VelosiAstUnit,
    osspec: &VelosiAst,
    relations: &Relations,
    outdir: &mut PathBuf,
) -> Result<(), VelosiCodeGenError> {
    match unit {
        VelosiAstUnit::Segment(segment) => {
            // outdir.push(segment.ident().to_lowercase());
            segment::generate(segment.as_ref(), relations, osspec, outdir)
                .expect("code generation failed\n");
            // outdir.pop();
        }
        VelosiAstUnit::StaticMap(staticmap) => {
            // outdir.push(staticmap.ident().to_lowercase());
            staticmap::generate(staticmap.as_ref(), relations, osspec, outdir)
                .expect("code generation failed\n");
            // outdir.pop();
        }
        VelosiAstUnit::Enum(e) => {
            // outdir.push(e.ident().to_lowercase());
            enums::generate(e.as_ref(), relations, osspec, outdir)
                .expect("code generation failed\n");
            // outdir.pop();
        }
        VelosiAstUnit::OSSpec(_) => panic!("osspec in module"),
    }

    Ok(())
}
