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

use crate::ast::{Ast, Field, State};
use crate::codegen::CodeGenBackend;
use crate::codegen::CodeGenError;

mod field;
mod interface;
mod utils;

use field::field_type;
use utils::{add_header, save_scope};

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

    fn generate_fields(
        &self,
        outdir: &PathBuf,
        unitname: &str,
        fields: &Vec<Field>,
    ) -> Result<(), CodeGenError> {
        let fieldsdir = outdir.join("fields");

        fs::create_dir_all(&fieldsdir)?;

        for f in fields {
            println!("generate interfaces fields");
            field::generate(unitname, f, &fieldsdir)?;
        }

        // generate the mod file.
        // the code generation scope
        let mut scope = CG::Scope::new();

        let title = format!("Module for all fields of unit '{}'", unitname);
        add_header(&mut scope, &title);

        // TODO: add doc comment

        scope.new_comment("modules");
        for f in fields {
            scope.raw(&format!("pub mod {};", f.name.to_lowercase()));
        }

        scope.new_comment("re-exports");
        for f in fields {
            scope.raw(&format!(
                "pub use {}::{};",
                f.name.to_lowercase(),
                field_type(f)
            ));
        }

        save_scope(scope, &fieldsdir, "mod")
    }
}

impl CodeGenBackend for BackendRust {
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

    fn generate_globals(&self, ast: &Ast) -> Result<(), CodeGenError> {
        for _const in &ast.consts {}
        Ok(())
    }

    fn generate_interfaces(&self, ast: &Ast) -> Result<(), CodeGenError> {
        // get the source dir
        let mut srcdir = self.outdir.join("src");

        for unit in &ast.units {
            srcdir.push(unit.name.to_lowercase());
            // the root directory as supplied by backend
            fs::create_dir_all(&srcdir)?;

            match &unit.state {
                State::MemoryState {
                    bases: _, fields, ..
                } => self
                    .generate_fields(&srcdir, &unit.name, &fields)
                    .expect("field generation failed"),
                _ => (),
            }

            srcdir.pop();
        }
        Ok(())
    }

    fn generate_units(&self, ast: &Ast) -> Result<(), CodeGenError> {
        // get the source dir
        let mut srcdir = self.outdir.join("src");

        for unit in &ast.units {
            srcdir.push(unit.name.to_lowercase());

            // construct the scope
            let mut scope = CG::Scope::new();

            // the fields
            scope.raw("pub mod fields;");

            // save the scope
            save_scope(scope, &srcdir, "mod")?;

            srcdir.pop();
        }

        Ok(())
    }

    fn finalize(&self, ast: &Ast) -> Result<(), CodeGenError> {
        // construct the source directory
        let srcdir = self.outdir.join("src");

        // construct the scope
        let mut scope = CG::Scope::new();

        let title = format!("{} Library", self.pkgname);
        add_header(&mut scope, &title);

        // the modules
        scope.new_comment("modules");
        for unit in &ast.units {
            scope.raw(&format!("pub mod {};", unit.name.to_lowercase()));
        }

        scope.new_comment("re-exports");
        for unit in &ast.units {
            scope.raw(&format!("pub use {}::*;", unit.name.to_lowercase(),));
        }

        // save the scope
        save_scope(scope, &srcdir, "lib")
    }
}
