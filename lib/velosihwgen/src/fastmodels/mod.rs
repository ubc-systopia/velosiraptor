// Velosiraptor Compiler
//
//
// MIT License
//
// Copyright (c) 2022 The University of British Columbia, Vancouver, BC, Canada
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

//! # The FastModels Platform Generator
//!
//! This module contains a generator for a Arm FastModels component.

use std::collections::HashMap;
// the used external libraries
use std::fs;
use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

// other libraries
use crustal as C;

// the library
use crate::VelosiHwGenBackend;
use crate::VelosiHwGenError;
use crate::COPYRIGHT;
use velosiast::VelosiAst;
use velosicomposition::Relations;

// the generators
mod unit;
use unit::generate_unit_header;
mod registers;
use registers::{generate_register_header, generate_register_impl};

use self::unit::{unit_class_name, unit_header_file};

/// # The Arm FastModels Platform Module
///
/// This generator produces a component for the Arm FastModels simulator using the
/// `TranslationUnit` support library.
///
/// ## Generated File Structure
///
/// outdir/hw/fastmodels/Makefile
/// outdir/hw/fastmodels/<vrs>.lisa
/// outdir/hw/fastmodels/bootimg.bin
/// outdir/hw/fastmodels/<vrs>_registers.cpp
/// outdir/hw/fastmodels/<vrs>_registers.hpp
/// outdir/hw/fastmodels/platform/Platform.sgproj
/// outdir/hw/fastmodels/platform/Platform.lisa
///
/// for subunit in vrs:
///    outdir/hw/fastmodels/src/<subunit>.cpp
///
/// outdir/hw/fastmodels/fm-translation-framework/
/// outdir/hw/fastmodels/fm-translation-framework/accessmode.hpp
/// outdir/hw/fastmodels/fm-translation-framework/interface_base.hpp
/// outdir/hw/fastmodels/fm-translation-framework/logging.hpp
/// outdir/hw/fastmodels/fm-translation-framework/register_base.hpp
/// outdir/hw/fastmodels/fm-translation-framework/state_base.hpp
/// outdir/hw/fastmodels/fm-translation-framework/state_field_base.hpp
/// outdir/hw/fastmodels/fm-translation-framework/translation_unit_base.hpp
/// outdir/hw/fastmodels/fm-translation-framework/types.hpp

pub struct ArmFastModelsModule {
    outdir: PathBuf,
    support_dir: PathBuf,
    pkgname: String,
}

pub fn add_header_comment(scope: &mut C::Scope, unit: &str, comp: &str) {
    scope.push_doc_str(format!("The {} of the '{}' translation unit\n\n", comp, unit).as_str());
    scope.push_doc_str(COPYRIGHT);
    scope.push_doc_str("WARNING: This file is auto-generated by the Velosiraptor compiler.\n");
}

impl ArmFastModelsModule {
    pub fn new(hwdir: &Path, pkgname: String) -> ArmFastModelsModule {
        // the manifest dir may be different depending on where cargo was run from.
        // if it ends in the hwgen directory we can just add it otherwise we add the
        // path to the hwgen directory as well.
        let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_default();
        let support_dir = if manifest_dir.ends_with("lib/velosihwgen") {
            Path::new(&manifest_dir).join("src/fastmodels/support")
        } else {
            Path::new(&manifest_dir).join("lib/velosihwgen/src/fastmodels/support")
        };

        ArmFastModelsModule {
            outdir: hwdir.join("fastmodels"),
            support_dir,
            pkgname,
        }
    }
}

fn copy_recursive(src: impl AsRef<Path>, dst: impl AsRef<Path>) -> std::io::Result<()> {
    fs::create_dir_all(&dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        if ty.is_dir() {
            copy_recursive(entry.path(), dst.as_ref().join(entry.file_name()))?;
        } else {
            fs::copy(entry.path(), dst.as_ref().join(entry.file_name()))?;
        }
    }
    Ok(())
}

// Find-and-replace for support files
fn fill_template(
    src: impl AsRef<Path>,
    dst: impl AsRef<Path>,
    subs: HashMap<&String, &String>,
) -> std::io::Result<()> {
    let mut data = String::new();
    let mut f = File::open(src).unwrap();
    f.read_to_string(&mut data)?;

    for (k, v) in subs {
        data = data.replace(k, v);
    }

    let mut out = File::create(dst)?;
    let _n = out.write(data.as_bytes())?;

    Ok(())
}

impl VelosiHwGenBackend for ArmFastModelsModule {
    fn prepare(&self) -> Result<(), VelosiHwGenError> {
        fs::create_dir_all(self.outdir.join("src"))?;
        fs::create_dir_all(self.outdir.join("platform"))?;

        copy_recursive(
            self.support_dir.join("fm_translation_framework"),
            self.outdir.join("fm_translation_framework"),
        )?;

        Ok(())
    }

    fn generate(&self, ast: &VelosiAst) -> Result<(), VelosiHwGenError> {
        let relations = Relations::from_ast(ast);
        let top_files = Vec::from_iter(relations.get_roots());
        if top_files.len() != 1 {
            panic!("!= 1 root unit found");
        }

        let top_file = unit_header_file(top_files[0]); // e.g. X86_MMU_unit.hpp
        let top_class = unit_class_name(top_files[0]); // e.g. X86_MMU

        fill_template(
            self.support_dir.join("TranslationUnit.lisa.template"),
            self.outdir.join(format!("{}.lisa", self.pkgname)),
            HashMap::from([
                (&"/* REPLACE top_class */".to_string(), &top_class),
                (&"/* REPLACE top_file */".to_string(), &top_file),
            ]),
        )?;

        fill_template(
            self.support_dir.join("Platform.lisa.template"),
            self.outdir.join("platform/Platform.lisa"),
            HashMap::from([(&"/* REPLACE top_class */".to_string(), &top_class)]),
        )?;

        fill_template(
            self.support_dir.join("Platform.sgproj.template"),
            self.outdir.join("platform/Platform.sgproj"),
            HashMap::from([(&"/* REPLACE pkgname */".to_string(), &self.pkgname)]),
        )?;

        fill_template(
            self.support_dir.join("Makefile.template"),
            self.outdir.join("Makefile"),
            HashMap::from([
                (&"/* REPLACE top_file */".to_string(), &top_file),
                (&"/* REPLACE pkgname */".to_string(), &self.pkgname),
            ]),
        )?;

        // check all units for registers and put them in the main directory
        generate_register_header(&self.pkgname, ast, &self.outdir.join("src"))?;
        generate_register_impl(&self.pkgname, ast, &self.outdir.join("src"))?;

        for u in ast.units() {
            if u.is_abstract() {
                continue;
            }

            generate_unit_header(u, ast, &self.outdir.join("src"))?;
        }

        Ok(())
    }

    fn finalize(&self) -> Result<(), VelosiHwGenError> {
        Ok(())
    }
}
