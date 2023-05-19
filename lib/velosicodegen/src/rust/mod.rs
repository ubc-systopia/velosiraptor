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

//! Rust Code Generation Backend

use std::fs;
use std::fs::File;
use std::io::BufWriter;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;

use codegen_rs as CG;

use crate::VelosiCodeGenError;
use velosiast::{VelosiAst, VelosiAstUnit};

mod enums;
mod field;
mod interface;
mod segment;
mod staticmap;
mod utils;

use utils::{add_const_def, add_header, save_scope};

// the module name for the constants module
const MOD_CONSTS: &str = "consts";

/// The rust backend
///
/// # Generated File Structure
///
///  - outdir/pkgname/Cargo.toml            the library cargo.toml
///  - outdir/pkgname/src/lib.rs          the library file
///  - outdir/pkgname/src/<unit>/mod.rs        the unit module
///  - outdir/pkgname/src/<unit>/interface.rs  the interface
///  - outdir/pkgname/src/<unit>/fields/<field>.rs
pub struct BackendRust {
    outdir: PathBuf,
    pkgname: String,
}

impl BackendRust {
    pub fn new(pkgname: String, outdir: &Path) -> Self {
        let path = outdir.join("rust");
        BackendRust {
            outdir: path,
            pkgname,
        }
    }

    fn generate_tomlfile(&self, outfile: &Path) -> Result<(), VelosiCodeGenError> {
        // create the Cargo.toml
        let cargofile = File::create(outfile.join("Cargo.toml"))?;
        let mut cargo = BufWriter::new(cargofile);

        let mut lines = Vec::new();
        writeln!(
            lines,
            "# This file is auto generated by velosiraptor compiler. "
        )?;
        writeln!(lines, "[package]")?;
        writeln!(lines, "name = \"{}\"", self.pkgname)?;
        writeln!(
            lines,
            "description = \"Auto generated translation driver for '{}'.\"",
            self.pkgname
        )?;
        writeln!(lines, "license = \"MIT\"")?;
        writeln!(lines, "version = \"0.1.0\"")?;
        writeln!(
            lines,
            "authors = [\"Velosiraptor Compiler <no-reply@velosiraptor>\"]"
        )?;
        writeln!(lines, "edition = \"2018\"")?;
        writeln!(lines, "\n[dependencies]")?;
        writeln!(lines, "# none")?;

        cargo.write_all(&lines)?;
        cargo.flush()?;
        Ok(())
    }

    /// prepares the code generation for the Rust backend
    ///
    /// This will setup the output directories, create the Toml file and
    /// create the `src` directory.
    pub fn prepare(&self) -> Result<(), VelosiCodeGenError> {
        // create the output directory, if needed

        // create the package path
        fs::create_dir_all(&self.outdir)?;

        // generate the toml file
        self.generate_tomlfile(&self.outdir)?;

        // create the source directory
        let srcdir = self.outdir.join("src");
        fs::create_dir_all(srcdir)?;

        Ok(())
    }

    /// generates the global definitions.
    ///
    /// This will produce a file with all the globally defined constant definitions.
    /// The file won't be produced if there are no globally defined constants
    pub fn generate_globals(&self, ast: &VelosiAst) -> Result<(), VelosiCodeGenError> {
        let consts = ast.consts();

        // get the source directory
        let srcdir = self.outdir.join("src");

        // the code generation scope
        let mut scope = CG::Scope::new();

        // constant definitions
        let title = format!("Global Constant Definitions for `{}` package", self.pkgname);
        add_header(&mut scope, &title);

        // now add the constants
        for c in consts {
            add_const_def(&mut scope, c);
        }

        save_scope(scope, &srcdir, MOD_CONSTS)
    }

    pub fn generate_interfaces(&self, ast: &VelosiAst) -> Result<(), VelosiCodeGenError> {
        // get the source dir
        let mut srcdir = self.outdir.join("src");

        for unit in ast.segments() {
            if !unit.is_abstract {
                srcdir.push(unit.ident().to_lowercase());
                // the root directory as supplied by backend
                fs::create_dir_all(&srcdir)?;
                interface::generate(unit, &srcdir)?;
                srcdir.pop();
            }
        }
        Ok(())
    }

    /// Generates the units
    pub fn generate_units(&self, ast: &VelosiAst) -> Result<(), VelosiCodeGenError> {
        // get the source dir
        let mut srcdir = self.outdir.join("src");

        println!("##### rust generate_units");

        for unit in ast.units() {
            srcdir.push(unit.ident().to_lowercase());

            // construct the scope for the module file
            let mut scope = CG::Scope::new();

            let title = format!("{} translation unit module", unit.ident());
            add_header(&mut scope, &title);

            // the unit
            scope.raw("mod unit;");
            // the unit
            scope.raw("pub use unit::*;");

            // generate the unit
            match unit {
                VelosiAstUnit::Segment(segment) => {
                    if segment.is_abstract {
                        log::info!("Skipping abstract segment unit {}", segment.ident());
                        srcdir.pop();
                        continue;
                    } else {
                        // the fields
                        scope.raw("pub mod fields;");
                        // the interface
                        scope.raw("mod interface;");
                        scope.raw("pub use interface::*;");

                        fs::create_dir_all(&srcdir)?;
                        segment::generate(segment, &srcdir).expect("code generation failed\n");
                    }
                }
                VelosiAstUnit::StaticMap(staticmap) => {
                    fs::create_dir_all(&srcdir)?;
                    staticmap::generate(ast, staticmap, &srcdir).expect("code generation failed\n");
                }
                VelosiAstUnit::Enum(e) => {
                    fs::create_dir_all(&srcdir)?;
                    enums::generate(e, &srcdir).expect("code generation failed\n");
                }
            }

            // save the scope
            save_scope(scope, &srcdir, "mod")?;

            srcdir.pop();
        }

        Ok(())
    }

    /// Finalizes the code generation
    ///
    /// Here we just need to generate the `lib.rs` file that pulls in all other
    /// modules and constant definitions.
    /// This basically creates a `pub mod` statement for each unit,
    /// and also for for the constant definitions. It then also re-exports
    /// the defined constants and unit types using `pub use` statements.
    pub fn finalize(&self, ast: &VelosiAst) -> Result<(), VelosiCodeGenError> {
        // construct the source directory
        let srcdir = self.outdir.join("src");

        // construct the scope
        let mut scope = CG::Scope::new();

        let title = format!("{} Library", self.pkgname);
        add_header(&mut scope, &title);

        // import the constants
        scope.new_comment("import constant definitions ");

        scope.raw(&format!("pub mod {MOD_CONSTS};"));
        scope.raw(&format!("pub use {MOD_CONSTS}::*;"));

        // import the units
        scope.new_comment("import the unit modules");

        for unit in ast.units() {
            if !unit.is_abstract() {
                scope.raw(&format!("pub mod {};", unit.ident().to_lowercase()));

                scope.raw(&format!(
                    "pub use {}::{};",
                    unit.ident().to_lowercase(),
                    utils::to_struct_name(unit.ident(), None)
                ));
            }
        }

        // save the scope
        save_scope(scope, &srcdir, "lib")
    }
}
