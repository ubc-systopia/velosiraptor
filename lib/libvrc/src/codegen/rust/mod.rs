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

use codegen_rs as CG;

use crate::ast::{Ast, Field, Interface, State};
use crate::codegen::CodeGenBackend;
use crate::codegen::CodeGenError;

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
    outdir: Option<String>,
    pkgname: String,
    usedirs: Vec<String>,
}

impl BackendRust {
    pub fn new(pkgname: String, outdir: Option<String>) -> Self {
        let outdir = match outdir {
            Some(p) => Some(String::from(Path::new(&p).join(&pkgname).to_str().unwrap())),
            None => None,
        };
        BackendRust {
            outdir,
            pkgname,
            usedirs: Vec::new(),
        }
    }

    fn to_struct_name(s: &str) -> String {
        String::from(s)
    }

    fn to_const_name(s: &str) -> String {
        String::from(s)
    }

    fn to_rust_type(l: u64) -> &'static str {
        match l {
            0..=8 => "u8",
            9..=16 => "u16",
            17..=32 => "u32",
            33..=64 => "u64",
            _ => "unknown",
        }
    }

    fn mask_str(m: u64, len: u64) -> String {
        match len {
            0..=8 => format!("0x{:02x}", (m & 0xff) as u8),
            9..=16 => format!("0x{:04x}", (m & 0xffff) as u16),
            17..=32 => format!("0x{:08x}", (m & 0xffffffff) as u32),
            33..=64 => format!("0x{:016x}", (m & 0xffffffffffffffff) as u64),
            _ => String::from("unknown"),
        }
    }

    fn generate_field(&self, field: &Field) {
        // a field is a struct
        //
        // field_name  --> struct FieldName {  val: u64 };
        //
        //

        let fname = format!("Field: {}", field.name);

        let sname = BackendRust::to_struct_name(&field.name);
        let maskname = format!("{}_MASK", BackendRust::to_const_name(&field.name));

        let mut scope = CG::Scope::new();

        // adding the header
        let mut lic = CG::License::new("FOOBAR", CG::LicenseType::Mit);
        lic.add_copyright("2021 Systopia Lab, Computer Science, University of British Columbia");
        scope.license(lic);

        // adding the autogenerated warning
        scope.new_comment("THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER");

        // adding hte constant for the mask value
        let mconst = scope.new_const(
            &maskname,
            Self::to_rust_type(field.nbits()),
            &format!("0x{:x}", field.mask_value()),
        );
        mconst.doc(vec!["the mask value for the interface fields"]);

        // create the struct
        let st = scope.new_struct(&sname);

        // add the doc field to the struct
        st.doc(&format!(
            "Represents the interface field '{}', defined in: {}",
            field.name, field.pos
        ));

        let valtype = Self::to_rust_type(field.nbits());
        // it has a single field, called 'val'
        st.field("val", valtype);

        // new implementation
        let imp = scope.new_impl(&sname);

        // add the new() function
        imp.new_fn("new")
            .vis("pub")
            .doc(&format!("creates a new {} value", field.name))
            .ret(CG::Type::new("Self"))
            .line("Self { val: 0 }");

        // add the get/set functions
        for sl in &field.layout {
            let fnname = format!("extract_{}", sl.name);
            let ftype = Self::to_rust_type(sl.nbits());

            // get function
            imp.new_fn(&fnname)
                .vis("pub")
                .doc(&format!(
                    "extracts value {}.{} from field",
                    field.name, sl.name
                ))
                .arg_ref_self()
                .ret(CG::Type::new(ftype))
                .line(format!(
                    "((self.val >> {}) & {}) as {}",
                    sl.start,
                    Self::mask_str((1 << sl.nbits()) - 1, sl.nbits()),
                    ftype
                ));

            let fnname = format!("insert_{}", sl.name);

            // set function
            imp.new_fn(&fnname)
                .vis("pub")
                .arg_mut_self()
                .arg("val", CG::Type::new(ftype))
                .doc(&format!(
                    "inserts value {}.{} in field",
                    field.name, sl.name
                ))
                .line(format!(
                    "self.val = (self.val & {}) | (((val as {}) & {}) << {})",
                    Self::mask_str(!sl.mask_value(), field.nbits()),
                    valtype,
                    Self::mask_str((1 << sl.nbits()) - 1, sl.nbits()),
                    sl.start
                ));
        }
        // println!("===========================================");
        // println!("{}", scope.to_string());
        // println!("===========================================");

        // assemble the
        if let Some(p) = &self.outdir {
            // the root directory
            let mut path = Path::new(p).to_path_buf();
        } else {
            println!("{:?}", scope.to_string())
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
    fn prepare(&self) -> Result<(), CodeGenError> {
        // create the output directory, if needed
        if let Some(p) = &self.outdir {
            // the root directory as supplied by backend
            let outdir = Path::new(p);

            // create the package path
            fs::create_dir_all(&outdir)?;

            // generate the toml file
            self.generate_tomlfile(&outdir)?;

            // create the source directory
            let srcdir = outdir.join("src");

            fs::create_dir_all(&srcdir)?;
        }
        Ok(())
    }
    fn generate_globals(&self, ast: &Ast) -> Result<(), CodeGenError> {
        for _const in &ast.consts {}
        Ok(())
    }

    fn generate_interfaces(&self, ast: &Ast) -> Result<(), CodeGenError> {
        for unit in &ast.units {
            match &unit.state {
                State::MemoryState { bases, fields, pos } => {
                    for f in fields {
                        self.generate_field(f)
                    }
                }
                _ => (),
            }
        }
        Ok(())
    }

    fn generate_units(&self, _ast: &Ast) -> Result<(), CodeGenError> {
        Ok(())
    }

    fn finalize(&self) -> Result<(), CodeGenError> {
        if let Some(p) = &self.outdir {
            // the root directory
            let mut path = Path::new(p).to_path_buf();

            path.push("src");
            path.push("lib.rs");

            // create the Cargo.toml
            let librs = File::create(path)?;

            let mut librs = BufWriter::new(librs);

            let mut lines = Vec::new();
            writeln!(lines, "\n")?;
            for u in &self.usedirs {
                writeln!(lines, "pub use {}", u)?;
            }

            librs.write_all(&lines)?;
            librs.flush()?;
        }
        Ok(())
    }
}
