// Velosiraptor Code Generator
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

use std::fs;
use std::path::Path;
use std::path::PathBuf;

use crustal as C;

use velosiast::{VelosiAst, VelosiAstUnit};
use velosicomposition::Relations;

use crate::VelosiCodeGenError;

use utils::{add_const_def, add_header};

mod enums;
mod field;
mod interface;
mod segment;
mod staticmap;
mod utils;

/// The C backend
///
/// # Generated File Structure
///
///  - outdir/pkgname/Cargo.toml            the library cargo.toml
///  - outdir/pkgname/src/lib.rs          the library file
///  - outdir/pkgname/src/<unit>/mod.rs        the unit module
///  - outdir/pkgname/src/<unit>/interface.rs  the interface
///  - outdir/pkgname/src/<unit>/fields/<field>.rs
pub struct BackendC {
    outdir: PathBuf,
    pkgname: String,
}

impl BackendC {
    pub fn new(pkgname: String, outdir: &Path) -> Self {
        let outdir = outdir.join("clang");
        BackendC { outdir, pkgname }
    }

    /// prepares the code generation for the C/CPP backend
    ///
    /// This will setup the output directories
    pub fn prepare(&self) -> Result<(), VelosiCodeGenError> {
        // create the package path
        fs::create_dir_all(&self.outdir)?;
        Ok(())
    }

    /// generates the global definitions.
    ///
    /// This will produce a file with all the globally defined constant definitions.
    /// The file won't be produced if there are no globally defined constants
    pub fn generate_globals(&self, ast: &VelosiAst) -> Result<(), VelosiCodeGenError> {
        // the code generation scope
        let mut scope = C::Scope::new();

        // constant definitions
        let title = format!("Global Constant Definitions for `{}` package", self.pkgname);
        add_header(&mut scope, &title);

        let hdrguard = format!("{}_CONSTS_H_", self.pkgname.to_uppercase());
        let guard = scope.new_ifdef(&hdrguard);
        let s = guard.guard().then_scope();

        let consts = ast.consts();

        // now add the constants
        let mut n_const = 0;
        for (i, c) in consts.enumerate() {
            add_const_def(s, c);
            n_const = i;
        }

        if n_const == 0 {
            s.new_comment("No global constants defined");
        }

        scope.set_filename("consts.h");
        scope.to_file(&self.outdir, true)?;

        Ok(())
    }

    pub fn generate_interfaces(&self, ast: &VelosiAst) -> Result<(), VelosiCodeGenError> {
        let srcdir = self.outdir.clone();
        interface::generate(ast, srcdir)
    }

    pub fn generate_units(&self, ast: &VelosiAst) -> Result<(), VelosiCodeGenError> {
        let mut srcdir = self.outdir.clone();
        let relations = Relations::from_ast(ast);

        for unit in ast.units() {
            match unit {
                VelosiAstUnit::Segment(segment) => {
                    if segment.is_abstract {
                        log::info!("Skipping abstract segment unit {}", segment.ident());
                        continue;
                    }
                    srcdir.push(segment.ident().to_lowercase());
                    segment::generate(segment, &relations, &srcdir)
                        .expect("code generation failed\n");
                    srcdir.pop();
                }
                VelosiAstUnit::StaticMap(staticmap) => {
                    srcdir.push(staticmap.ident().to_lowercase());
                    staticmap::generate(ast, staticmap, &relations, &srcdir)
                        .expect("code generation failed\n");
                    srcdir.pop();
                }
                VelosiAstUnit::Enum(e) => {
                    srcdir.push(e.ident().to_lowercase());
                    enums::generate(ast, e, &srcdir).expect("code generation failed\n");
                    srcdir.pop();
                }
                VelosiAstUnit::OSSpec(_) => todo!(),
            }
        }

        Ok(())
    }
    pub fn finalize(&self, _ast: &VelosiAst) -> Result<(), VelosiCodeGenError> {
        Ok(())
    }
}
