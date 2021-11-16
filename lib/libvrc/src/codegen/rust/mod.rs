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

use crate::ast::{AstRoot, Field, Interface, InterfaceField};
use crate::codegen::CodeGenBackend;
use crate::codegen::CodeGenError;

mod field;
mod interface;
mod unit;
mod utils;

use field::field_type;
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
        BackendRust {
            outdir: outdir.join(&pkgname),
            pkgname,
        }
    }

    fn generate_tomlfile(&self, outfile: &Path) -> Result<(), CodeGenError> {
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
}

impl CodeGenBackend for BackendRust {
    /// prepares the code generation for the Rust backend
    ///
    /// This will setup the output directories, create the Toml file and
    /// create the `src` directory.
    fn prepare(&self) -> Result<(), CodeGenError> {
        // create the output directory, if needed

        // create the package path
        fs::create_dir_all(&self.outdir)?;

        // generate the toml file
        self.generate_tomlfile(&self.outdir)?;

        // create the source directory
        let srcdir = self.outdir.join("src");
        fs::create_dir_all(&srcdir)?;

        Ok(())
    }

    /// generates the global definitions.
    ///
    /// This will produce a file with all the globally defined constant definitions.
    /// The file won't be produced if there are no globally defined constants
    fn generate_globals(&self, ast: &AstRoot) -> Result<(), CodeGenError> {
        // no need to create anything if there are no constants defined
        if ast.consts.is_empty() {
            return Ok(());
        }

        // get the source directory
        let srcdir = self.outdir.join("src");

        // the code generation scope
        let mut scope = CG::Scope::new();

        // constant definitions
        let title = format!("Global Constant Definitions for `{}` package", self.pkgname);
        add_header(&mut scope, &title);

        // now add the constants
        for c in &ast.consts {
            add_const_def(&mut scope, c);
        }

        save_scope(scope, &srcdir, MOD_CONSTS)
    }

    fn generate_interfaces(&self, ast: &AstRoot) -> Result<(), CodeGenError> {
        // get the source dir
        let mut srcdir = self.outdir.join("src");

        for unit in &ast.units {
            srcdir.push(unit.name.to_lowercase());
            // the root directory as supplied by backend
            fs::create_dir_all(&srcdir)?;
            interface::generate(unit, &srcdir)?;
            srcdir.pop();
        }
        Ok(())
    }

    /// Generates the units
    fn generate_units(&self, ast: &AstRoot) -> Result<(), CodeGenError> {
        // get the source dir
        let mut srcdir = self.outdir.join("src");

        for unit in &ast.units {
            srcdir.push(unit.name.to_lowercase());

            // generate the unit
            unit::generate(unit, &srcdir)?;

            // construct the scope
            let mut scope = CG::Scope::new();

            let title = format!("{} translation unit module", unit.name);
            add_header(&mut scope, &title);

            // the fields
            scope.raw("pub mod fields;");
            // the unit
            scope.raw("mod unit;");

            // the unit
            scope.raw("pub use unit :: *;");

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
    fn finalize(&self, ast: &AstRoot) -> Result<(), CodeGenError> {
        // construct the source directory
        let srcdir = self.outdir.join("src");

        // construct the scope
        let mut scope = CG::Scope::new();

        let title = format!("{} Library", self.pkgname);
        add_header(&mut scope, &title);

        // import the constants
        scope.new_comment("import constant definitions ");
        if !ast.consts.is_empty() {
            scope.raw(&format!("pub mod {};", MOD_CONSTS));
        } else {
            scope.new_comment("no constants defined");
        }

        // re-export the constants
        scope.new_comment("re-export the constants directly");
        if !ast.consts.is_empty() {
            scope.raw(&format!("pub use {}::*;", MOD_CONSTS));
        } else {
            scope.new_comment("no constants defined");
        }

        // impor the units
        scope.new_comment("import the unit modules");
        if !ast.units.is_empty() {
            for unit in &ast.units {
                scope.raw(&format!("pub mod {};", unit.name.to_lowercase()));
            }
        } else {
            scope.new_comment("no unit definitions to import");
        }

        // reexport the
        scope.new_comment("re-export the unit types directly");
        for unit in &ast.units {
            scope.raw(&format!(
                "pub use {}::{};",
                unit.name.to_lowercase(),
                unit.name
            ));
        }

        // save the scope
        save_scope(scope, &srcdir, "lib")
    }
}
