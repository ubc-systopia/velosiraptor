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
use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

use crustal as C;

use velosiast::VelosiAst;
use velosicomposition::Relations;

use crate::VelosiCodeGenError;

use utils::{add_const_def, add_header};

mod field;
mod interface;
mod osspec;
mod unit;
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
    supportdir: PathBuf,
    pkgname: String,
}

impl BackendC {
    pub fn new(pkgname: String, outdir: &Path) -> Self {
        let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_default();
        let supportdir = if manifest_dir.ends_with("lib/velosicodegen") {
            Path::new(&manifest_dir)
                .parent()
                .and_then(|f| f.parent())
                .unwrap()
                .join("support")
                .to_path_buf()
        } else {
            Path::new(&manifest_dir).join("support").to_path_buf()
        };

        let outdir = outdir.join("clang");
        BackendC {
            outdir,
            pkgname,
            supportdir,
        }
    }

    /// prepares the code generation for the C/CPP backend
    ///
    /// This will setup the output directories
    pub fn prepare(&self, _osspec: &VelosiAst) -> Result<(), VelosiCodeGenError> {
        // create the package path
        fs::create_dir_all(&self.outdir)?;
        Ok(())
    }

    fn generate_types(
        &self,
        ast: &VelosiAst,
        _osspec: &VelosiAst,
    ) -> Result<(), VelosiCodeGenError> {
        // the code generation scope
        let mut scope = C::Scope::new();

        // constant definitions
        let title = format!("Global Constant Definitions for `{}` package", self.pkgname);
        add_header(&mut scope, &title);

        let hdrguard = format!("{}_CONSTS_H_", self.pkgname.to_uppercase());
        let guard = scope.new_ifdef(&hdrguard);
        let s = guard.guard().then_scope();

        s.new_include("stdint.h", true);

        ////////////////////////////////////////////////////////////////////////////////////////////
        // Types
        ////////////////////////////////////////////////////////////////////////////////////////////

        let relations = Relations::from_ast(ast);
        let roots = relations.get_root_units();
        if roots.len() != 1 {
            panic!("assumed one root unit!");
        }

        let inbitwidth = roots[0].input_bitwidth();
        let outbitwidth = roots[0].output_bitwidth();

        let vaddr_type_width = if inbitwidth > 32 {
            64
        } else if inbitwidth > 16 {
            32
        } else if inbitwidth > 8 {
            16
        } else {
            8
        };

        let paddr_type_width = if outbitwidth > 32 {
            64
        } else if outbitwidth > 16 {
            32
        } else if outbitwidth > 8 {
            16
        } else {
            8
        };

        let size_type_width = std::cmp::max(vaddr_type_width, paddr_type_width);

        s.new_typedef(utils::VADDR_TYPE, C::Type::new_uint(vaddr_type_width));
        s.new_typedef(utils::PADDR_TYPE, C::Type::new_uint(paddr_type_width));
        s.new_typedef(utils::GENADDR_TYPE, C::Type::new_uint(size_type_width));
        s.new_typedef(utils::SIZE_TYPE, C::Type::new_uint(size_type_width));

        ////////////////////////////////////////////////////////////////////////////////////////////
        // Flags
        ////////////////////////////////////////////////////////////////////////////////////////////

        if let Some(flags) = ast.flags() {
            s.new_comment("Defined unit flags");

            let st = s.new_struct(utils::FLAGS_NAME);

            for flag in &flags.flags {
                let f = st.new_field(flag.ident(), C::Type::new_uint64());
                f.set_bitfield_width(1);
            }
        } else {
            s.new_comment("No defined flags");
            s.new_struct(utils::FLAGS_NAME);
        }

        s.new_typedef(utils::FLAGS_TYPE, C::Type::new_struct(utils::FLAGS_NAME));

        let m = scope.new_macro("DEFAULT_FLAGS");
        m.set_value("(flags_t) { 0 }");

        scope.set_filename("types.h");
        scope.to_file(&self.outdir, true)?;
        Ok(())
    }

    fn generate_consts(
        &self,
        ast: &VelosiAst,
        osspec: &VelosiAst,
    ) -> Result<(), VelosiCodeGenError> {
        // the code generation scope
        let mut scope = C::Scope::new();

        // constant definitions
        let title = format!("Global Constant Definitions for `{}` package", self.pkgname);
        add_header(&mut scope, &title);

        let hdrguard = format!("{}_CONSTS_H_", self.pkgname.to_uppercase());
        let guard = scope.new_ifdef(&hdrguard);
        let s = guard.guard().then_scope();

        s.new_include("stdint.h", true);

        ////////////////////////////////////////////////////////////////////////////////////////////
        // Global constants
        ////////////////////////////////////////////////////////////////////////////////////////////

        let consts: Vec<_> = ast.consts().collect();
        if !consts.is_empty() {
            s.new_comment("Global constant definitions");
            for c in consts {
                add_const_def(s, c);
            }
        } else {
            s.new_comment("No global constants defined");
        }

        ////////////////////////////////////////////////////////////////////////////////////////////
        // OSSpec Constants
        ////////////////////////////////////////////////////////////////////////////////////////////

        let consts: Vec<_> = osspec.consts().collect();
        if !consts.is_empty() {
            s.new_comment("OS Spec constant definitions");
            for c in consts {
                add_const_def(s, c);
            }
        } else {
            s.new_comment("No OS Spec constants defined");
        }

        scope.set_filename("consts.h");
        scope.to_file(&self.outdir, true)?;
        Ok(())
    }

    /// generates the global definitions.
    ///
    /// This will produce a file with all the globally defined constant definitions.
    /// The file won't be produced if there are no globally defined constants
    pub fn generate_globals(
        &self,
        ast: &VelosiAst,
        osspec: &VelosiAst,
    ) -> Result<(), VelosiCodeGenError> {
        self.generate_consts(ast, osspec)
            .expect("generating consts failed");
        self.generate_types(ast, osspec)
            .expect("generating types failed");

        Ok(())
    }

    pub fn generate_interfaces(
        &self,
        ast: &VelosiAst,
        osspec: &VelosiAst,
    ) -> Result<(), VelosiCodeGenError> {
        let mut srcdir = self.outdir.clone();
        let relations = Relations::from_ast(ast);

        let env = osspec.osspec().unwrap();

        let units = if env.has_map_protect_unmap() {
            relations.get_group_root_units()
        } else {
            ast.units().filter(|u| !u.is_abstract()).cloned().collect()
        };

        for unit in units {
            debug_assert!(!unit.is_abstract());
            interface::generate(&unit, osspec, &mut srcdir)?;
        }

        Ok(())
    }

    pub fn generate_units(
        &self,
        ast: &VelosiAst,
        osspec: &VelosiAst,
    ) -> Result<(), VelosiCodeGenError> {
        let mut srcdir = self.outdir.clone();
        let relations = Relations::from_ast(ast);

        let env = osspec.osspec().unwrap();

        let units = if env.has_map_protect_unmap() {
            relations.get_group_root_units()
        } else {
            ast.units().filter(|u| !u.is_abstract()).cloned().collect()
        };

        for unit in units {
            debug_assert!(!unit.is_abstract());
            unit::generate(&unit, osspec, &relations, &mut srcdir)?;
        }

        Ok(())
    }
    pub fn finalize(
        &self,
        _ast: &VelosiAst,
        _osspec: &VelosiAst,
    ) -> Result<(), VelosiCodeGenError> {
        let src = self.supportdir.join("mmio.h");
        let dst = self.outdir.join("os_mmio.h");
        std::fs::copy(src, dst)?;

        let src = self.supportdir.join("registers.h");
        let dst = self.outdir.join("os_registers.h");
        std::fs::copy(src, dst)?;

        let src = self.supportdir.join("memory.h");
        let dst = self.outdir.join("os_memory.h");
        std::fs::copy(src, dst)?;

        Ok(())
    }

    pub fn test_compile(&self, ast: &VelosiAst, osspec: &VelosiAst) -> Result<(), String> {
        let relations = Relations::from_ast(ast);

        let env = osspec.osspec().unwrap();

        osspec::generate(env, self.outdir.as_path());

        let driverfile = self.outdir.join("driver.c");

        let mut file = File::create(driverfile.clone()).expect("create file failed");

        file.write_all(b"#include<stdint.h>\n")
            .expect("write failed");
        file.write_all(b"#include<stdbool.h>\n")
            .expect("write failed");
        file.write_all(b"#include<stdlib.h>\n")
            .expect("write failed");

        for root in relations.get_root_units() {
            let include = format!(
                "# include \"{}_unit.h\"\n",
                root.ident().to_ascii_lowercase()
            );
            file.write_all(include.as_bytes()).expect("write failed");
        }

        file.write_all(b"int main() { return 0;} \n\n")
            .expect("write failed");

        // run make
        let res = Command::new("gcc")
            .current_dir(self.outdir.clone())
            .arg("-fsyntax-only")
            .arg("-I")
            .arg(".")
            .arg("driver.c")
            .output()
            .expect("failed to execute gcc!");

        if !res.status.success() {
            let res = String::from_utf8(res.stderr).unwrap();
            return Err(res);
        }

        Ok(())
    }
}
